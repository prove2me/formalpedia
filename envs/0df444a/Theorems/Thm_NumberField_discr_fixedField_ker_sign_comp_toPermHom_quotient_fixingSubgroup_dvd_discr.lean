-- Prove2me | Theorems.Thm_NumberField_discr_fixedField_ker_sign_comp_toPermHom_quotient_fixingSubgroup_dvd_discr
-- name    : NumberField.discr_fixedField_ker_sign_comp_toPermHom_quotient_fixingSubgroup_dvd_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/6ca5dfea-515a-5ca2-9ad4-af5241f53bc4
-- title:
--   Discriminant of the quadratic resolvent divides d_K
-- statement:
--   Let $L$ be a number field that is Galois over $\mathbb{Q}$, and let $K$ be a number field equipped with an embedding into $L$ over $\mathbb{Q}$ (an algebra structure making $\mathbb{Q} \to K \to L$ a tower). Write $G = L \simeq_{\mathrm{alg}[\mathbb{Q}]} L$ for the Galois group of $L/\mathbb{Q}$, and let $H$ be the fixing subgroup of the intermediate field $\mathrm{im}(K \to L)$, the field range of the $\mathbb{Q}$-algebra map $K \to L$; thus $H = \mathrm{Gal}(L/K)$. The group $G$ acts by left translation on the coset space $G/H$, giving a homomorphism $G \to \mathrm{Perm}(G/H)$, and composing with the sign character $\mathrm{Perm}(G/H) \to \mathbb{Z}^{\times}$ yields $\varepsilon : G \to \mathbb{Z}^{\times}$. The assertion is that the discriminant of the number field $L^{\ker \varepsilon}$, the fixed field of $\ker\varepsilon$ inside $L$, divides the discriminant of $K$ in $\mathbb{Z}$.
--
--   The fixed field of $\ker\varepsilon$ is the quadratic resolvent $\mathbb{Q}(\sqrt{d_K})$ of $K$ (equal to $\mathbb{Q}$ when $d_K$ is a square), so the statement expresses the classical fact that $d_K$ is $d_k$ times a square, of which Hasse's relation $d_K = d_{k}f^2$ for cubic fields is the case $[K:\mathbb{Q}]=3$. It is deduced from Hilbert's discriminant formula in the form [`NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0`](thm.html#NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0), applied to $H = \mathrm{Gal}(L/K)$ and to $H = \ker\varepsilon$, and is used in the construction of admissible twists with prescribed local behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_discr_fixedField_ker_sign_comp_toPermHom_quotient_fixingSubgroup_dvd_discr.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain
open NumberField

open scoped Classical in

theorem NumberField.discr_fixedField_ker_sign_comp_toPermHom_quotient_fixingSubgroup_dvd_discr
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (K : Type) [Field K] [NumberField K] [Algebra K L] [IsScalarTower ℚ K L] :
    discr ↥(IntermediateField.fixedField
        ((Equiv.Perm.sign : Equiv.Perm ((L ≃ₐ[ℚ] L) ⧸ (IsScalarTower.toAlgHom ℚ K L).fieldRange.fixingSubgroup) →* ℤˣ).comp
          (MulAction.toPermHom (L ≃ₐ[ℚ] L)
            ((L ≃ₐ[ℚ] L) ⧸ (IsScalarTower.toAlgHom ℚ K L).fieldRange.fixingSubgroup))).ker) ∣ discr K := by sorry
