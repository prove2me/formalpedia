-- Prove2me | Theorems.Thm_OceanicGames_Interior_eq_4_4_4_5
-- name    : OceanicGames.Interior.eq_4_4_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:31.328599+00:00
-- url     : https://prove2.me/theorems/532fc8e6-afd9-4048-aba8-92918bc35dcf
-- title:
--   (4.4)–(4.5), p. 10 — Σφ_i(y) = Prob{F′(y) = 0} and Φ(y) = Prob{F′(y) = 1/α}
-- statement:
--   Let $\alpha > 0$, $w_1, \dots, w_m \ge 0$, and $0 < y < w(M) + \alpha$. For a uniformly random point $x \in I^m$, let $F(y) = \inf\{ t \ge 0 : w(P(t)) + \alpha t \ge y\}$ be the pivot location of the game $\Gamma(y) = [y; w_1, \dots, w_m; \alpha]$, viewed as a function of the quota. Then:
--
--   1. with probability 1, $F$ is differentiable at $y$;
--   2. the major players' total value is
--   $$\sum_{i=1}^m \varphi_i(y) = \operatorname{Prob}\{ F'(y) = 0 \};$$
--   3. the ocean's value is
--   $$\Phi(y) = \operatorname{Prob}\{ F'(y) = 1/\alpha \}.$$
--
--   Thus the quota $y$ falls on a flat piece of $F$ (a major player's jump) or on a piece of slope $1/\alpha$ (the ocean), and these two events carry the major players' and the ocean's value.
--
--   **Formalization Note** "$F'(y) = v$" is stated as `HasDerivAt` (two-sided derivative equal to $v$), so a point where $F$ is not differentiable belongs to neither event. Because the derivative is two-sided, $y$ ranges over the open interval $(0, w(M) + \alpha)$. $\Phi(y) = 1 - \sum_i \varphi_i(y)$ by (2.5).
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §4, (4.4)–(4.5), p. 10

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- (4.4)–(4.5), p. 10: for `0 < y < w(M) + α`, `F(y)` is differentiable at `y` with
probability 1, `Σ φ_i(y) = Prob {F'(y) = 0}` and `Φ(y) = Prob {F'(y) = 1/α}`. -/
theorem eq_4_4_4_5 {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 < y) (hyW : y < wsum w Finset.univ + α) :
    volume {x | x ∈ cube m ∧ ¬ DifferentiableAt ℝ (fun z => pivotLoc α w x z) y} = 0 ∧
    ∑ i, value y α w i =
      (volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) 0 y}).toReal ∧
    oceanValue y α w =
      (volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) (1 / α) y}).toReal := by sorry

end OceanicGames.Interior
