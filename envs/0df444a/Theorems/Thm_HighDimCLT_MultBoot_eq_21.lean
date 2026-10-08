-- Prove2me | Theorems.Thm_HighDimCLT_MultBoot_eq_21
-- name    : HighDimCLT.MultBoot.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T08:38:30.696996+00:00
-- url     : https://prove2.me/theorems/a07b4cae-444b-4884-8936-9c2153608fdc
-- title:
--   (21), p. 2325 — 0 ≤ F_β(w) − max_j(w_j − y_j) ≤ β⁻¹ log p, for every β > 0
-- statement:
--   Let $p\ge 3$, $\beta>0$ and $y\in\mathbb R^p$, and define the smooth max
--   $$F_\beta(w)=\beta^{-1}\log\Big(\sum_{j=1}^p\exp\big(\beta(w_j-y_j)\big)\Big),\qquad w\in\mathbb R^p.$$
--   Then for every $w\in\mathbb R^p$,
--   $$0\le F_\beta(w)-\max_{1\le j\le p}(w_j-y_j)\le\beta^{-1}\log p.$$
--
--   The smooth max is a differentiable surrogate for the indicator of $\{w\le y\}$; this sandwich controls the error of the substitution.
--
--   **Formalization Note** The page states (21) with $\beta=\phi\log p$, so that $\beta^{-1}\log p=\phi^{-1}$; the proof of Theorem 4.1 (p. 2342) uses it for every $\beta>0$, which is what is stated. The maximum over $j$ is a supremum over the finite set $\{1,\dots,p\}$.
-- source:
--   Chernozhukov, Chetverikov and Kato, Central limit theorems and bootstrap in high dimensions, Ann. Probab. 45 (2017), p. 2325, App. B, display (21); used for β > 0 at p. 2342, App. E.2

import Mathlib
import Definitions.Def_HighDimCLT_MultBoot_Setting

namespace HighDimCLT.MultBoot

open MeasureTheory ProbabilityTheory

universe u

/-- **Display (21)**, App. B, p. 2325 (used for every `β > 0` in App. E.2, p. 2342): the smooth
max `F_β(w) = β^{-1} log ∑_j exp(β(w_j − y_j))` satisfies
`0 ≤ F_β(w) − max_j (w_j − y_j) ≤ β^{-1} log p` for all `w ∈ ℝ^p`. -/
theorem eq_21 (p : ℕ) (hp : 3 ≤ p) (β : ℝ) (hβ : 0 < β) (y w : EuclideanSpace ℝ (Fin p)) :
    0 ≤ Fβ β y w - (⨆ j : Fin p, (w j - y j)) ∧
      Fβ β y w - (⨆ j : Fin p, (w j - y j)) ≤ β⁻¹ * Real.log p := by sorry

end HighDimCLT.MultBoot
