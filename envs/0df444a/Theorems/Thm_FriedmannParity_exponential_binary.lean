-- Prove2me | Theorems.Thm_FriedmannParity_exponential_binary
-- name    : FriedmannParity.exponential_binary
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:12:03.932573+00:00
-- url     : https://prove2.me/theorems/8ea6d266-9175-4323-b9c8-cd25247ce1b8
-- title:
--   Exponential lower bounds with binary outdegree
-- statement:
--   For each of the local and global rules, uniform linear-edge hard families with linearly bounded priorities can be chosen with at most two distinct outgoing neighbors per vertex. Complete executions exist and every such execution takes at least $2^n$ updates.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §7.2 binary-outdegree refinement and §8.4 corresponding global-rule refinement

import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_binary : ExponentialBinary := by sorry

end FriedmannParity
