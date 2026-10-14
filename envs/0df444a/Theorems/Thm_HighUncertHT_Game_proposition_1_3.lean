-- Prove2me | Theorems.Thm_HighUncertHT_Game_proposition_1_3
-- name    : HighUncertHT.Game.proposition_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:29.449626+00:00
-- url     : https://prove2.me/theorems/6e959c02-67c5-47f5-94c2-43fc870a352a
-- title:
--   Proposition 1.3, p. 10 — u is nonnegative, non-decreasing and convex
-- statement:
--   Let $u$ be a classical solution of (HJB). Then $u$ is nonnegative, non-decreasing and convex on $[0,\infty)$:
--   $$
--   u(w)\ge0\ (w\ge0),\qquad u\ \text{non-decreasing on }[0,\infty),\qquad u\ \text{convex on }[0,\infty).
--   $$
--
--   Convexity gives $u''\ge0$, which determines which extreme points of $\mathrm{ch}(K^\ell)$ the maximizing adversary uses, and nonnegativity makes $u(0)$ a legitimate limit for the nonnegative costs $V^n$.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 10, Proposition 1.3

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_HJB

namespace HighUncertHT.Game

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Proposition 1.3, p. 10: the classical solution `u` of (HJB) is nonnegative, non-decreasing
and convex on `[0, ∞)`. -/
theorem proposition_1_3 {L : ℕ} (S : Setting L) (u : ℝ → ℝ) (hu : IsClassicalSolution S u) :
    (∀ w : ℝ, 0 ≤ w → 0 ≤ u w) ∧ MonotoneOn u (Set.Ici 0) ∧ ConvexOn ℝ (Set.Ici 0) u := by sorry

end HighUncertHT.Game
