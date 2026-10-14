-- Prove2me | Theorems.Thm_HighUncertHT_Game_eq_47
-- name    : HighUncertHT.Game.eq_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:04.010975+00:00
-- url     : https://prove2.me/theorems/2844d5ca-f0da-4b4c-a204-2f2e3f7aa6ad
-- title:
--   (47), p. 28 — limsup Cⁿ(β*ⁿ(aⁿ), aⁿ) ≤ V(0) = u(0) for every control sequence
-- statement:
--   Let $u$ be the classical solution of (HJB). For every sequence of admissible controls $a^n\in\mathcal A^n$,
--   $$
--   \limsup_{n\to\infty}C^n(\beta^{*n}(a^n),a^n)\le u(0).
--   $$
--
--   Since $V^n\le\sup_{a^n}C^n(\beta^{*n}(a^n),a^n)$, this gives the upper bound $\limsup_nV^n\le u(0)$ of the goal theorem.
--
--   **Formalization Note** The page bounds the limit superior by $\mathsf V(0)$, the value of the martingale control problem at $0$; it is stated here with $u(0)$, equal to $\mathsf V(0)$ by Proposition 1.1.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 28, display (47)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Control
import Definitions.Def_HighUncertHT_Game_Priority
import Definitions.Def_HighUncertHT_Game_HJB

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- (47), p. 28: for every sequence of controls `aⁿ ∈ 𝒜ⁿ`,
`limsup_n Cⁿ(β^{*n}(aⁿ), aⁿ) ≤ V(0)`, stated with `V(0) = u(0)` for the classical solution `u` of
(HJB) (Proposition 1.1). -/
theorem eq_47 {L : ℕ} (S : Setting L) (u : ℝ → ℝ) (hu : IsClassicalSolution S u)
    (f : (n : ℕ) → AdversaryControl S n) :
    limsup (fun n => cost S n (betaStar S n) (f n)) atTop ≤ ENNReal.ofReal (u 0) := by sorry

end HighUncertHT.Game
