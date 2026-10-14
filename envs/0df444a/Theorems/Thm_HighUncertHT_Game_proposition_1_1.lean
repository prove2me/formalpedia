-- Prove2me | Theorems.Thm_HighUncertHT_Game_proposition_1_1
-- name    : HighUncertHT.Game.proposition_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:19.958136+00:00
-- url     : https://prove2.me/theorems/5cb2858c-f7f4-4485-b0a6-f8e8553a05e0
-- title:
--   Proposition 1.1, p. 10 — (HJB) has a unique classical solution u
-- statement:
--   For every setting, the HJB equation
--   $$
--   \sum_{\ell=1}^L H^\ell(u'(w),u''(w))-u(w)+w=0,\qquad w\ge0,
--   $$
--   with $u'(0)=0$ and $\limsup_{w\to\infty}|u(w)|/w<\infty$, has a classical ($C^2$) solution $u$, and any two classical solutions agree on $[0,\infty)$.
--
--   The solution $u$ is the limiting value function of the game. Existence and uniqueness make the goal theorem, stated for "the classical solution $u$", non-vacuous and unambiguous.
--
--   **Formalization Note** Only the first sentence of Proposition 1.1 is formalized; its "Moreover, $\mathsf V=u$" concerns the martingale control problem, which is not part of this mission.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 10, Proposition 1.1 (first sentence)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_HJB

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Proposition 1.1, p. 10 (first sentence): the HJB equation has a unique classical solution
on `[0, ∞)`. -/
theorem proposition_1_1 {L : ℕ} (S : Setting L) :
    ∃ u : ℝ → ℝ, IsClassicalSolution S u ∧
      ∀ v : ℝ → ℝ, IsClassicalSolution S v → Set.EqOn v u (Set.Ici 0) := by sorry

end HighUncertHT.Game
