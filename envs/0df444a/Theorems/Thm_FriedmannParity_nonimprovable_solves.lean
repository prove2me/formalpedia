-- Prove2me | Theorems.Thm_FriedmannParity_nonimprovable_solves
-- name    : FriedmannParity.nonimprovable_solves
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:10:55.594247+00:00
-- url     : https://prove2.me/theorems/b265f193-28b6-47bf-8237-acbee0da9d6d
-- title:
--   Winning regions at a terminal strategy
-- statement:
--   For a non-improvable legal strategy, even and odd dominating cycle priorities identify exactly the two positional winning regions. The current player-0 strategy wins on its region; every optimal player-1 counterstrategy wins on the other region; and the current strategy has pointwise greatest valuation.
-- source:
--   Oliver Friedmann, An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms, LMCS 2011, author PDF https://oliverfriedmann.com/downloads/papers/strategy_improvement_lower_bound_journal.pdf; arXiv:1106.0778v2 https://arxiv.org/abs/1106.0778; §3, Theorem 3.3, all five conclusions

import Definitions.Def_friedmann_parity

set_option autoImplicit false

namespace FriedmannParity

theorem nonimprovable_solves {V : Type} [Fintype V] [DecidableEq V]
    (G : Game V) (hG : WellFormed G) (σ : V → V)
    (hσ : Legal G false σ) (hstop : ¬ Improvable G σ) :
    (WinningRegion G false = {v | (value G σ v).cyclePriority % 2 = 0}) ∧
    (WinningRegion G true = {v | (value G σ v).cyclePriority % 2 = 1}) ∧
    (∀ v, (value G σ v).cyclePriority % 2 = 0 → Wins G false σ v) ∧
    (∀ τ, OptimalCounterstrategy G σ τ →
      ∀ v, (value G σ v).cyclePriority % 2 = 1 → Wins G true τ v) ∧
    (∀ ρ, Legal G false ρ → ∀ v, ValueLE G (value G ρ v) (value G σ v)) := by sorry

end FriedmannParity
