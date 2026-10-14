-- Prove2me | Theorems.Thm_HighUncertHT_Game_theorem_2_1
-- name    : HighUncertHT.Game.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:37:23.233213+00:00
-- url     : https://prove2.me/theorems/bd94827d-4d37-47ba-839b-c9bc2d613254
-- title:
--   Theorem 2.1, p. 10 — the game value Vⁿ converges to V(0) = u(0)
-- statement:
--   For every setting, let $u$ be the classical solution of the HJB equation. Then the value of the $n$-th scheduling game converges:
--   $$
--   V^n=\inf_{\beta^n\in\mathbb B^n}\sup_{a^n\in\mathcal A^n}C^n(\beta^n(a^n),a^n)\longrightarrow u(0)\qquad(n\to\infty).
--   $$
--
--   This identifies the asymptotic value of the game between the scheduler and an adversary who chooses job-size distributions from uncertainty classes whose variances are uncertain at order one: it is the value at $0$ of a one-dimensional HJB equation for a reflected diffusion whose drift and variance the adversary controls.
--
--   **Formalization Note** The page states $V^n\to\mathsf V(0)=u(0)$, with $\mathsf V$ the value of the martingale control problem; the goal is stated in its $u(0)$ form (Proposition 1.1 identifies $\mathsf V$ with $u$). Values are in $[0,\infty]$, and $u(0)\ge0$ by Proposition 1.3.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 10, Theorem 2.1

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_System
import Definitions.Def_HighUncertHT_Game_Strategy
import Definitions.Def_HighUncertHT_Game_Control
import Definitions.Def_HighUncertHT_Game_HJB

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Theorem 2.1, p. 10: the value of the `n`-th game converges, `Vⁿ → V(0) = u(0)`, stated with
the classical solution `u` of (HJB) (Proposition 1.1 gives its existence and uniqueness and
`V = u`). -/
theorem theorem_2_1 {L : ℕ} (S : Setting L) (u : ℝ → ℝ) (hu : IsClassicalSolution S u) :
    Tendsto (fun n => value S n) atTop (𝓝 (ENNReal.ofReal (u 0))) := by sorry

end HighUncertHT.Game
