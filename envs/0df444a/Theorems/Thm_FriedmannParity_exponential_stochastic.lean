-- Prove2me | Theorems.Thm_FriedmannParity_exponential_stochastic
-- name    : FriedmannParity.exponential_stochastic
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:11:56.193802+00:00
-- url     : https://prove2.me/theorems/77b833e2-fca3-47e9-8add-83f2fce51a3a
-- title:
--   Exponential stochastic strategy iteration
-- statement:
--   Both local and global strategy improvement have uniform linear-edge families of stopping stochastic games on which complete executions exist and every complete execution makes at least $2^n$ updates.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §9, final simple-stochastic-game lower-bound corollary

import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_stochastic : FriedmannStochastic.Exponential := by sorry

end FriedmannParity
