-- Prove2me | Theorems.Thm_FriedmannParity_exponential_deterministic
-- name    : FriedmannParity.exponential_deterministic
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:12:31.28267+00:00
-- url     : https://prove2.me/theorems/46723e52-4b56-4e70-a981-331709e496c2
-- title:
--   Exponential lower bounds for deterministic strategy iteration
-- statement:
--   Finite parity, discounted-payoff, mean-payoff-through-reduction, and stopping stochastic games admit the exponential local and global strategy-iteration lower bounds specified in the public models. The bounds use uniform linear edge count, actual legal initial strategies, existence of completed executions, and a lower bound on every completed execution.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §§6–9, local/global lower bounds, linear-edge refinements, and payoff/stochastic extensions

import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannParity

theorem exponential_deterministic :
    ExponentialLocal ∧ ExponentialGlobal ∧ FriedmannDiscounted.Exponential ∧
      FriedmannDiscounted.ExponentialMeanViaReduction ∧ FriedmannStochastic.Exponential := by sorry

end FriedmannParity
