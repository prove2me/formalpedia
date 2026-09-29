-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
-- name    : NumberField.PlaceDecomp.map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/3a1dc960-f33a-5ad7-a2cb-73695fd96887
-- title:
--   Vanishing local coordinate at an unramified place
-- statement:
--   Let $E$ and $F$ be number fields with $F/E$ Galois, let $w$ be a height-one prime of $\mathcal O_F$, and let $D_w =$ `decomp E F w` be the decomposition subgroup of $\mathrm{Gal}(F/E)$ attached to the valuation subring of the $w$-adic valuation of $F$. Assume the ramification index `Ideal.ramificationIdx'` of the contraction of $w$ to $\mathcal O_E$ in $w$ is $1$. Let $\rho$ be a morphism of $D_w$-representations from the restriction along $D_w \hookrightarrow \mathrm{Gal}(F/E)$ of the multiplicative-action representation on $F^\times$ to the multiplicative-action representation of $D_w$ on $(F_w)^\times$, where $F_w$ is the $w$-adic completion, and assume (hypothesis `hρ`) that on underlying elements $\rho$ is induced by the unit map of $F \to F_w$. Let $b\colon \mathrm{Gal}(F/E)^2 \to F^\times$ (written additively) be a $2$-cocycle for the representation on $F^\times$, all of whose values are of finite order in $F^\times$. Then the cohomology class of $b$ in $H^2(\mathrm{Gal}(F/E), F^\times)$, restricted to $D_w$ and then pushed forward along $\rho$, is $0$ in $H^2(D_w, (F_w)^\times)$.
--
--   This is the statement that a Brauer-type class represented by a root-of-unity-valued $2$-cocycle has trivial local coordinate at a place unramified in $F/E$: the values lie in the local units, whose Tate cohomology vanishes in the unramified case (the cited vanishing result for `tateCohomology` of $(\mathcal O_{F_w})^\times$). It feeds the computation [`NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside`](thm.html#NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside), where local coordinates of a descended Kummer class are shown to be supported on the places above a finite set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (w : HeightOneSpectrum (𝓞 F))
    (hunr : Ideal.ramificationIdx' (Ideal.comap (algebraMap (𝓞 E) (𝓞 F)) w.asIdeal) w.asIdeal = 1)
    (ρ : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hρ : ∀ u : Fˣ, ρ.hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap F (w.adicCompletion F)).toMonoidHom u))
    (b : (F ≃ₐ[E] F) × (F ≃ₐ[E] F) → Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)
    (hb : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))
    (hfin : ∀ g : (F ≃ₐ[E] F) × (F ≃ₐ[E] F), IsOfFinOrder (Additive.toMul (b g) : Fˣ)) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) ρ 2).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype
        (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ))) 2).hom
          ((H2π (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) Fˣ)).hom ⟨b, hb⟩)) = 0 := by sorry
