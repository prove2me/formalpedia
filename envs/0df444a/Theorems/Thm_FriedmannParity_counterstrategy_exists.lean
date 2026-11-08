-- Prove2me | Theorems.Thm_FriedmannParity_counterstrategy_exists
-- name    : FriedmannParity.counterstrategy_exists
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:10:36.013051+00:00
-- url     : https://prove2.me/theorems/763cd554-9e90-4874-b9a8-d703947b182c
-- title:
--   Optimal replies and attained valuations
-- statement:
--   For every finite total parity game with distinct priorities and every legal positional player-0 strategy, one legal positional player-1 reply simultaneously minimizes the play valuation at all starting vertices and realizes the defined valuation.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §3, Lemma 3.1, existence clause and definition of the game valuation

import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem counterstrategy_exists {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V) (hσ : Legal G false σ) :
    ∃ τ, OptimalCounterstrategy G σ τ ∧ ∀ v, value G σ v = playValue G σ τ v := by sorry

end FriedmannParity
