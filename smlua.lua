--------------------------------------------------------------------------------
-- This is a State machine implementation by Lua
--------------------------------------------------------------------------------

local SM_EMPTY_SIG = -5;
local SM_ENTRY_SIG = -4;
local SM_EXIT_SIG  = -3;
local SM_INIT_SIG  = -2;
local SM_USER_SIG  = -1;

local sm_reserved_event =
{
	[SM_EMPTY_SIG] = { sig = SM_EMPTY_SIG, event = nil },
	[SM_ENTRY_SIG] = { sig = SM_ENTRY_SIG, event = nil },
	[SM_EXIT_SIG]  = { sig = SM_EXIT_SIG , event = nil },
	[SM_INIT_SIG]  = { sig = SM_INIT_SIG , event = nil },
	[SM_USER_SIG]  = { sig = SM_USER_SIG , event = nil },
};

local function SM_TRIG(me, state, sig)
	return state(me, sm_reserved_event[sig]);
end

local function SM_ENTRY(me, state)
	return SM_TRIG(me, state, SM_ENTRY_SIG);
end

local function SM_EXIT(me, state)
	return SM_TRIG(me, state, SM_EXIT_SIG);
end

-----------------------------------
-- Export
function IS_EMPTY_SIG(sig)
	return sig == SM_EMPTY_SIG;
end
function IS_ENTRY_SIG(sig)
	return sig == SM_ENTRY_SIG;
end
function IS_EXIT_SIG(sig)
	return sig == SM_EXIT_SIG;
end
function IS_INIT_SIG(sig)
	return sig == SM_INIT_SIG;
end
function IS_USER_SIG(sig)
	return sig >= SM_USER_SIG;
end

--------------------------------------------------------------------------------

local SM_RET_HANDLED   = 0;
local SM_RET_IGNORE    = 1;
local SM_RET_UNHANDLED = 2;
local SM_RET_TRAN      = 3;
local SM_RET_SUPER     = 4;

-- Export
function SM_HANDLED()
	return SM_RET_HANDLED;
end
function SM_IGNORE()
	return SM_RET_IGNORE;
end
function SM_UNHANDLED()
	return SM_RET_UNHANDLED;
end
function SM_TRAN(me, target)
	me.temp = target;
	return SM_RET_TRAN;
end
function SM_SUPER(me, super)
	me.temp = super;
	return SM_RET_SUPER;
end

--------------------------------------------------------------------------------

local function sm_new(s, t)
	local sm = {};

	sm.state = s;
	sm.temp  = t;

	return sm;
end

function sm_event_new( s, e )
	local event = {};

	event.sig = s;
	event.event = e;

	return event;
end

--------------------------------------------------------------------------------
-- 	                              FSM
--------------------------------------------------------------------------------

local function fsm_init(self, e)
	local ret = nil;

	ret = self.temp(self, e);
	if ret ~= SM_RET_TRAN then
		return ret;
	end

	SM_ENTRY(self, self.temp);

	self.state = self.temp;

	return ret;
end

local function fsm_dispatch(self, e)
	local ret = nil;

	ret = self.temp(self, e);
	if ret == SM_RET_TRAN then
		SM_EXIT(self, self.state);
		SM_ENTRY(self, self.temp);
		self.state = self.temp;
	end
end

function fsm_new(init)
	local fsm = sm_new(nil, init);

	fsm.init = fsm_init;
	fsm.dispatch = fsm_dispatch;

	return fsm;
end

--------------------------------------------------------------------------------
--                              HSM
--------------------------------------------------------------------------------

local function hsm_find_path(me, t, s, path)
	local ip = -1;
	local iq = nil;
	local ret = nil;

	-- (a) check source == target (transition to self)
	if s == t then
		SM_EXIT(me, s);
		ip = 0;
	else
		SM_TRIG(me, t, SM_EMPTY_SIG);
		t = me.temp;

		-- (b) check source == target->super
		if s == t then
			ip = 0;
		else
			SM_TRIG(me, s, SM_EMPTY_SIG);

			-- (c) check source->super == target->super
			if t == me.temp then
				SM_EXIT(me, s);
				ip = 0;
			else
				-- (d) check source->super == target
				if me.temp == path[0] then
					SM_EXIT(me, s);
				else
					-- (e) check rest of spurce == target->super->super...
					-- and stor the entry path along the way
					ip = 1;
					iq = 0;
					path[1] = t;
					t = me.temp;

					-- find target->super->super...
					ret = SM_TRIG(me, path[1], SM_EMPTY_SIG);
					while ret == SM_RET_SUPER do
						ip = ip + 1;
						path[ip] = me.temp;
						if s == me.temp then
							iq = 1;
							ip = ip - 1;
							ret = SM_RET_HANDLED;
						else
							ret = SM_TRIG(me, me.temp, SM_EMPTY_SIG);
						end
					end

					-- the LCA not found yet?
					if 0 == iq then
						SM_EXIT(me, s);

						-- (f)
						iq = ip;
						ret = SM_RET_IGNORE;
						repeat
							s = path[iq];
							-- is this the LCA?
							if t == s then
								ret = SM_RET_HANDLED;
								ip = iq - 1;
								iq = -1;
							else
								iq = iq - 1; -- try lower super state of target
							end
						until iq < 0;

						-- LCA not found?
						if ret ~= SM_RET_HANDLED then
							-- (g)
							ret = SM_RET_IGNORE;
							repeat
								if SM_EXIT(me, t) == SM_RET_HANDLED then
									SM_TRIG(me, t, SM_EMPTY_SIG);
								end
								t = me.temp;
								iq = ip;
								repeat
									s = path[iq];
									if t == s then
										ip = iq - 1;
										iq = -1;
										ret = SM_RET_HANDLED; -- break
									else
										iq = iq - 1;
									end
								until iq < 0;
							until ret == SM_RET_HANDLED;
						end
					end
				end
			end
		end
	end

	return ip;
end

local function hsm_init(self, e)
	local ret, ip;

	local path = {};
	local t = self.state;

	ret = self.temp(self, e);

	repeat
		ip = 0;

		path[0] = self.temp;
		SM_TRIG(self, self.temp, SM_EMPTY_SIG);
		while t ~= self.temp do
			ip = ip + 1;
			path[ip] = self.temp;
			SM_TRIG(self, self.temp, SM_EMPTY_SIG);
		end
		self.temp = path[0];

		repeat
			SM_ENTRY(self, path[ip]);
			ip = ip -1;
		until ip < 0;

		t = path[0];
	until SMTRIG(self, t, SM_INIT_SIG) ~= SM_RET_TRAN;

	self.temp = t;
	self.state = self.temp;
end

local function hsm_dispatch(self, e)
	local t = self.state;
	local s = nil;

	local ret = nil;

	repeat
		s = self.temp;
		ret = s(self, e); 	--调用状态处理函数
		if ret == SM_RET_UNHANDLED then
			ret = SM_TRIG(self, s, SM_EMPTY_SIG);
		end
	until ret ~= SM_RET_SUPER;

	--如果发生状态转换
	if ret == SM_RET_TRAN then
		local path = {};
		local ip = -1;

		path[0] = self.temp;
		path[1] = t;

		while s ~= t do
			ret = SM_EXIT(self, t);
			if ret == SM_RET_HANDLED then
				SM_TRIG(self, t, SM_EMPTY_SIG);
			end
			t = self.temp;
		end

		ip = hsm_find_path(self, path[0], s, path);
		while ip >= 0 do
			SM_ENTRY(self, path[ip]);
			ip = ip - 1;
		end

		t = path[0];
		self.temp = t;

		while SM_TRIG(self, t, SM_INIT_SIG) == SM_RET_TRAN do
			ip = 0;
			path[0] = self.temp;

			SM_TRIG(self, self.temp, SM_EMPTY_SIG);
			while t ~= self.temp do
				ip = ip + 1;
				path[ip] = self.temp;
				SM_TRIG(self, self.temp, SM_EMPTY_SIG);
			end
			self.temp = path[0];

			repeat
				SM_ENTRY(self, path[ip]);
				ip = ip - 1;
			until ip < 0;

			t = path[0];
		end
	end

	self.temp = t;
	self.state = t;
end

local function hsm_top(self, e)
	return SM_IGNORE();
end

function hsm_new(init)
	local hsm = sm_new(hsm_top, init);

	hsm.init = hsm_init;
	hsm.dispatch = hsm_dispatch;

	return hsm;
end

--------------------------------------------------------------------------------
--                   END
--------------------------------------------------------------------------------

