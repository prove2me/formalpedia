-- Prove2me | Theorems.Thm_IntermediateField_exists_mulEquiv_fixedField_apply_eq
-- name    : IntermediateField.exists_mulEquiv_fixedField_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/60c99cd4-b6c6-547a-ac3f-04a87c12a8dd
-- title:
--   Galois correspondence H ≅ Gal(F/F^H), pinned on values
-- statement:
--   Let $E$ and $F$ be fields with $F$ an $E$-algebra, and assume $F$ is finite-dimensional over $E$ and Galois over $E$; let $H$ be a subgroup of the group $F \simeq_{\mathrm{alg}[E]} F$ of $E$-algebra automorphisms of $F$. Write $F^{H} =$ `IntermediateField.fixedField H` for the intermediate field of $F/E$ consisting of the elements of $F$ fixed by every member of $H$. The assertion is that there exists a group isomorphism $\Theta$ from $H$, regarded as a group in its own right via its coercion to a type, onto the group $F \simeq_{\mathrm{alg}[F^{H}]} F$ of $F^{H}$-algebra automorphisms of $F$, which is pinned on values: for every $s \in H$ and every $y \in F$ one has $\Theta(s)(y) = s(y)$, where on the right $s$ is viewed as an $E$-algebra automorphism of $F$. So the isomorphism is not merely abstract; it is restriction of the underlying map of $F$, with the only change being the base field over which linearity is recorded.
--
--   This is the standard half of the fundamental theorem of Galois theory identifying a subgroup $H$ of $\operatorname{Gal}(F/E)$ with $\operatorname{Gal}(F/F^{H})$, stated in the value-pinned form needed when elements of $H$ and of $\operatorname{Gal}(F/F^{H})$ must be used interchangeably in cocycle and norm computations. It serves as a bookkeeping step in the Sylow-type descent from $p$-group layers to an arbitrary finite Galois layer, and is cited by [`M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_mulEquiv_fixedField_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IntermediateField.exists_mulEquiv_fixedField_apply_eq
    (E F : Type) [Field E] [Field F] [Algebra E F] [FiniteDimensional E F] [IsGalois E F] (H : Subgroup (F ≃ₐ[E] F)) :
    ∃ Θ : ↥H ≃* (F ≃ₐ[↥(IntermediateField.fixedField H)] F), ∀ (s : ↥H) (y : F), Θ s y = (s : F ≃ₐ[E] F) y := by sorry
