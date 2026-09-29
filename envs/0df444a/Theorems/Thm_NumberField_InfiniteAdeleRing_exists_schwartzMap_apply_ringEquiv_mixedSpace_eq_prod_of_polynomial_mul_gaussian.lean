-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
-- name    : NumberField.InfiniteAdeleRing.exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/31515498-3c9e-5e91-8d84-ea0a9c1487df
-- title:
--   Factorisable polynomial-times-Gaussian archimedean functions are Schwartz
-- statement:
--   Let $F$ be a number field and let $\Phi$ assign to each infinite place $w$ of $F$ a function $\Phi_w \colon (\mathrm{Fin}\,2 \to F_w) \to \mathbb{C}$ on pairs of elements of the completion $F_w$. Assume that each $\Phi_w$ is a polynomial times a Gaussian in the following sense: there is a polynomial $P$ over $\mathbb{C}$ in the variables indexed by $\mathrm{Fin}\,2 \sqcup \mathrm{Fin}\,2$ such that for every $y \colon \mathrm{Fin}\,2 \to F_w$ one has $\Phi_w(y) = P\bigl(\iota_w(y_0),\iota_w(y_1),\overline{\iota_w(y_0)},\overline{\iota_w(y_1)}\bigr)\cdot \exp\bigl(-\pi \sum_i \|y_i\|^2\bigr)$, where $\iota_w$ is the embedding `Completion.extensionEmbedding` of $F_w$ into $\mathbb{C}$, the bar is complex conjugation, and the real numbers $\|y_i\|^2$ are cast into $\mathbb{C}$. The conclusion is that there exists a Schwartz function $g \in \mathcal{S}\bigl((\mathrm{Fin}\,2 \to \mathbb{R}^{r_1}\times\mathbb{C}^{r_2}),\mathbb{C}\bigr)$ on pairs of points of the mixed space of $F$, with complex values, such that for every pair $y \colon \mathrm{Fin}\,2 \to \mathbb{A}_{F,\infty}$ of infinite adeles, $g$ evaluated at the pair of images of $y_0,y_1$ under the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` from $\mathbb{A}_{F,\infty}$ to the mixed space equals the product $\prod_{w \mid \infty} \Phi_w\bigl(i \mapsto (y_i)_w\bigr)$ over all infinite places.
--
--   This is the archimedean input for factorisable Schwartz–Bruhat functions: it records that a product over the archimedean places of polynomial-times-Gaussian functions of the local variables, transported through the standard identification of the infinite adeles with the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$, is realised by a genuine Schwartz function of the joint archimedean variable. It is used by [`AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite`](thm.html#AutomorphicForm.exists_sum_mul_prod_localZeta_bottomRow_eq_of_isArchKFinite) to supply the archimedean factor of a global test function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace
open scoped SchwartzMap

open scoped Classical in

theorem NumberField.InfiniteAdeleRing.exists_schwartzMap_apply_ringEquiv_mixedSpace_eq_prod_of_polynomial_mul_gaussian
    (F : Type) [Field F] [NumberField F]
    (Φ : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
    (_hΦ : ∀ w : InfinitePlace F, ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ w y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) P
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) :
    ∃ g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace F), ℂ),
      ∀ y : Fin 2 → InfiniteAdeleRing F,
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i)) = ∏ w, Φ w (fun i => y i w) := by sorry
