-- Prove2me | Theorems.Thm_FriedmannParity_exponential_payoff
-- name    : FriedmannParity.exponential_payoff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:11:44.073871+00:00
-- url     : https://prove2.me/theorems/0687195f-dd88-401e-b407-58c135e62f71
-- title:
--   Exponential payoff strategy iteration
-- statement:
--   Both local and global improvement require at least $2^n$ updates on uniform linear-edge families of discounted games. The same lower bound holds for mean-payoff inputs when the algorithm runs through the explicitly defined standard discounted reduction. Every hard instance admits a complete execution.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §9, payoff-game lower-bound corollary and standard mean-to-discounted reduction

import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_payoff : FriedmannDiscounted.Exponential ∧
    FriedmannDiscounted.ExponentialMeanViaReduction := by sorry

end FriedmannParity
