-- Prove2me | Theorems.Thm_OceanicGames_Interior_theorem_2
-- name    : OceanicGames.Interior.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:15:42.899464+00:00
-- url     : https://prove2.me/theorems/3fa36c60-996b-42ad-8fb5-f6e5278313a5
-- title:
--   Theorem 2 — the ocean's value is α times the slope of E{F(y)}
-- statement:
--   Let $\alpha > 0$ and $w_1, \dots, w_m \ge 0$, and write $W = w(M) + \alpha$. For the oceanic game $\Gamma(y) = [y; w_1, \dots, w_m; \alpha]$ with quota $y$, let $\Phi(y)$ be the combined value of the ocean and let $E\{F(y)\} = \int_{I^m} F(y)\, dx_1\cdots dx_m$ be the expected location of the pivot. Then for every $0 \le y \le W$,
--   $$\Phi(y) = \alpha \, \frac{d}{dy} E\{F(y)\},$$
--   the derivative being taken within $[0, W]$ (one-sided at the endpoints).
--
--   This identifies the ocean's value with the slope of a single explicit function of the quota; it is what lets the value of an added major player be written as an integral of $\Phi$ (the Lemma of §4).
--
--   **Formalization Note** The statement is `HasDerivWithinAt (E F) (Φ(y)/α) [0, W] y`, which is the paper's formula divided by $\alpha > 0$; at interior points it is the ordinary derivative. $\Phi(y) = 1 - \sum_i \varphi_i(y)$ by (2.5).
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), Theorem 2, (4.7), p. 11

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology

namespace OceanicGames.Interior

/-- Theorem 2, (4.7), p. 11: `Φ(y) = α (d/dy) E{F(y)}` for `0 ≤ y ≤ w(M) + α` (one-sided at the
endpoints). -/
theorem theorem_2 {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy : y ∈ Set.Icc 0 (wsum w Finset.univ + α)) :
    HasDerivWithinAt (expPivotLoc α w) (oceanValue y α w / α)
      (Set.Icc 0 (wsum w Finset.univ + α)) y := by sorry

end OceanicGames.Interior
