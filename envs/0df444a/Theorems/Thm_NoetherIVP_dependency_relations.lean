-- Prove2me | Theorems.Thm_NoetherIVP_dependency_relations
-- name    : NoetherIVP.dependency_relations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T14:58:48.491927+00:00
-- url     : https://prove2.me/theorems/ebe17811-deb0-4120-bbbd-e31f67befb3a
-- title:
--   Noether (1918), eq. (16): Theorem II dependencies among the Lagrange expressions
-- statement:
--   **Theorem II, equation (16) of the paper**, in the case of arbitrary functions entering to first
--   order ($\sigma = 1$). For an infinite continuous group the variations take the form
--   $$\delta u_i \;=\; a_i\,p \;+\; \sum_{l} b_{l i}\,\partial_l p$$
--   with $p$ an arbitrary function. Noether integrates the resulting relation (15) over a region,
--   choosing $p$ so that it and its derivatives vanish on the boundary, and concludes from the
--   arbitrariness of $p$ the $\rho$ identities
--   $$\sum_{i} a_i\,\psi_i \;-\; \sum_{l} \partial_l\Bigl(\sum_i b_{l i}\,\psi_i\Bigr) \;=\; 0 ,$$
--   dependencies between the Lagrange expressions and their first derivatives.
--
--   Formally: for continuous $\psi_i, a_i, b_{l i}$ with each $y \mapsto \sum_i b_{l i}\psi_i$ of class
--   $C^1$, if $\int \sum_i \psi_i\,(a_i p + \sum_l b_{l i}\,\partial_l p) = 0$ for every smooth compactly
--   supported $p$, then the displayed identity holds at every point.
-- source:
--   E. Noether, Invariante Variationsprobleme (1918), Tavel translation, arXiv:physics/0503066v3, §2, pp. 5-6, equations (14), (15) and (16), in the case sigma = 1.

import Mathlib
import Definitions.Def_NoetherIVP_core

namespace NoetherIVP
theorem dependency_relations {n m : ℕ} (psi a : Fin m → (Fin n → ℝ) → ℝ)
    (b : Fin n → Fin m → (Fin n → ℝ) → ℝ)
    (hpsi : ∀ i : Fin m, Continuous (psi i))
    (ha : ∀ i : Fin m, Continuous (a i))
    (hb : ∀ (l : Fin n) (i : Fin m), Continuous (b l i))
    (hG : ∀ l : Fin n, ContDiff ℝ 1 fun y => ∑ i : Fin m, b l i y * psi i y)
    (hint : ∀ p : (Fin n → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) p → HasCompactSupport p →
      (∫ y : Fin n → ℝ, ∑ i : Fin m,
          psi i y * (a i y * p y + ∑ l : Fin n, b l i y * dirD l p y)) = 0) :
    ∀ x : Fin n → ℝ, (∑ i : Fin m, a i x * psi i x)
      - ∑ l : Fin n, dirD l (fun y => ∑ i : Fin m, b l i y * psi i y) x = 0 := by sorry
end NoetherIVP
