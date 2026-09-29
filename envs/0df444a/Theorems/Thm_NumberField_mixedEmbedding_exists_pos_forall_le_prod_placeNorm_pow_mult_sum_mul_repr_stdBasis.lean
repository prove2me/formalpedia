-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis
-- name    : NumberField.mixedEmbedding.exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/673044e7-3a77-5947-8e7e-3c5ff712aea8
-- title:
--   Uniform lower bound for place-weighted products of ideal-lattice forms
-- statement:
--   Let $F$ be a number field and let $I$ be an invertible fractional ideal of $\mathcal{O}_F$ in $F$, i.e. a unit of the monoid of fractional ideals for the non-zero-divisors of $\mathcal{O}_F$. Write $J =$ `Module.Free.ChooseBasisIndex ℤ I` for the index type of the chosen $\mathbb{Z}$-basis of $I$, and recall that `fractionalIdealLatticeBasis F I` is the associated $\mathbb{R}$-basis of the mixed space of $F$ indexed by $J$, while `stdBasis F` is the standard $\mathbb{R}$-basis of that space, indexed by `index F`, the disjoint union of the set of real infinite places of $F$ with the product of the set of complex infinite places with `Fin 2`. For an integer vector $m \colon J \to \mathbb{Z}$ put $L(m)(i) = \sum_{j} m_j \cdot \big(\mathrm{fractionalIdealLatticeBasis}\, F\, I)^{\ast}_j(\mathrm{stdBasis}\, F\, i)\big)$, the $m$-weighted sum of the coordinates, in the ideal-lattice basis, of the $i$-th standard basis vector. The assertion is that there exists a real $\delta_0 > 0$ such that for every $m \colon J \to \mathbb{Z}$ with $m \neq 0$ one has $$\delta_0 \le \Big(\prod_{w \text{ real}} |L(m)(\mathrm{inl}\, w)|^{\mathrm{mult}(w)}\Big)\cdot \prod_{w \text{ complex}} \Big(\sqrt{L(m)(\mathrm{inr}(w,0))^2 + L(m)(\mathrm{inr}(w,1))^2}\Big)^{\mathrm{mult}(w)},$$ the products being over the real and the complex infinite places of $F$ and $\mathrm{mult}(w)$ being $1$ at a real and $2$ at a complex place.
--
--   This is a geometry-of-numbers separation statement for the lattice attached to a fractional ideal under the mixed embedding: the place-weighted product attached to a non-zero integral combination of the relevant coordinate forms, which is the absolute-norm-type quantity of a non-zero lattice vector, cannot be made arbitrarily small. It is used in the estimate [`AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn`](thm.html#AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn), where such a uniform positive lower bound over all non-zero frequency vectors gives rapid decay of a Fourier expansion term by term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis.lean

import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField nonZeroDivisors
open scoped Classical in

theorem NumberField.mixedEmbedding.exists_pos_forall_le_prod_placeNorm_pow_mult_sum_mul_repr_stdBasis
    {F : Type} [Field F] [NumberField F] (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    let L : (Module.Free.ChooseBasisIndex ℤ I → ℤ) → index F → ℝ := fun m i =>
      ∑ j, (m j : ℝ) * (fractionalIdealLatticeBasis F I).repr (stdBasis F i) j
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ m : Module.Free.ChooseBasisIndex ℤ I → ℤ, m ≠ 0 →
      δ₀ ≤ (∏ w : {w : InfinitePlace F // w.IsReal}, |L m (Sum.inl w)| ^ w.1.mult)
           * ∏ w : {w : InfinitePlace F // w.IsComplex},
             Real.sqrt ((L m (Sum.inr (w, 0)))^2 + (L m (Sum.inr (w, 1)))^2) ^ w.1.mult := by sorry
