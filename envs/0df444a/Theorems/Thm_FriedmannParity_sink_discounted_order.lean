-- Prove2me | Theorems.Thm_FriedmannParity_sink_discounted_order
-- name    : FriedmannParity.sink_discounted_order
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:12:19.165849+00:00
-- url     : https://prove2.me/theorems/5fae2ad3-42ba-4faf-8e48-9c24064bff92
-- title:
--   Preservation of valuation comparisons under reduction
-- statement:
--   In a finite injective-priority 1-sink game, take any legal strategy whose valuations are pointwise no worse than the initial strategy. Strict comparisons between the valuations of any two vertices agree exactly with strict comparisons of their values in the specified induced discounted game.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §9, valuation-comparison equivalence corollary following the optimal-counterstrategy correspondence

import Definitions.Def_friedmann_payoff

set_option autoImplicit false

namespace FriedmannParity

theorem sink_discounted_order {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (ι : V → V) (sink : V) (hSink : IsSinkGame G ι sink)
    (σ : V → V) (hσ : Legal G false σ)
    (hAbove : ∀ v, ValueLE G (value G ι v) (value G σ v)) (v w : V) :
    ValueLT G (value G σ v) (value G σ w) ↔
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ v <
      FriedmannScalar.value (FriedmannDiscounted.model (FriedmannDiscounted.induced G)) σ w := by sorry

end FriedmannParity
