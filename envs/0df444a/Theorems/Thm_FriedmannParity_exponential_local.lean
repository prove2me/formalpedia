-- Prove2me | Theorems.Thm_FriedmannParity_exponential_local
-- name    : FriedmannParity.exponential_local
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:11:08.132027+00:00
-- url     : https://prove2.me/theorems/a3f4402f-f312-4efc-bcfa-8bd6d5530d22
-- title:
--   Exponential local strategy improvement
-- statement:
--   There is a uniform linear-size family of finite total parity games with distinct, linearly bounded priorities and legal initial strategies such that complete local-update executions exist and every such execution performs at least $2^n$ improving updates.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §6, Theorem 6.14 together with §7.1 linear-edge refinement

import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_local : ExponentialLocal := by sorry

end FriedmannParity
