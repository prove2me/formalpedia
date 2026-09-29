-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal
-- name    : NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/1a2d08d0-bfa5-5390-8d68-20d98f10b6ae
-- title:
--   Splitting off a real coordinate of the mixed space, measure preservingly
-- statement:
--   Let $K$ be a number field and let $i_0$ be a real infinite place of $K$, i.e. an element of the subtype of infinite places $v$ with `v.IsReal`. The assertion is that there exists a continuous $\mathbb{R}$-linear isomorphism $e$ from the mixed space of $K$, namely $(\{v \text{ real}\} \to \mathbb{R}) \times (\{w \text{ complex}\} \to \mathbb{C})$, onto $\mathbb{R} \times \big((\{v \text{ real}, v \neq i_0\} \to \mathbb{R}) \times (\{w \text{ complex}\} \to \mathbb{C})\big)$, such that: first, $e$ is measure preserving from the volume (Lebesgue product) measure on the mixed space to the volume measure on the target product; and second, for every point $X$ of the mixed space the first component of $e X$ is the value $X.1\,i_0$ of the real part of $X$ at the place $i_0$. Thus the isomorphism isolates the $i_0$-coordinate as a single real factor, keeping the remaining real coordinates and all complex coordinates as the second factor, and does so without distorting Lebesgue measure.
--
--   A coordinate-regrouping lemma for the mixed space $K \otimes_{\mathbb{Q}} \mathbb{R} \cong \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ of a number field, used to apply Fubini's theorem in the variable attached to a chosen real place while treating the other coordinates as parameters. It is invoked in the construction of a compactly supported smooth function with prescribed logarithmic-potential integral at a real place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

open scoped Classical in

theorem NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isReal
    (K : Type) [Field K] [NumberField K] (i₀ : {v : NumberField.InfinitePlace K // v.IsReal}) :
    ∃ e : NumberField.mixedEmbedding.mixedSpace K ≃L[ℝ] (ℝ × (({v : {v : NumberField.InfinitePlace K // v.IsReal} // v ≠ i₀} → ℝ) × ({w : NumberField.InfinitePlace K // w.IsComplex} → ℂ))),
      MeasurePreserving e volume volume ∧
      ∀ X : NumberField.mixedEmbedding.mixedSpace K, (e X).1 = X.1 i₀ := by sorry
