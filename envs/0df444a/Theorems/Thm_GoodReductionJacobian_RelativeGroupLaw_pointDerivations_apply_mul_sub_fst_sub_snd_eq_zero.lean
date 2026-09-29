-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero
-- name    : GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/bb273b63-0f48-5ace-8a2b-77a30fe7ee8b
-- title:
--   Point derivations at the unit kill μ^sharp a-p₁^sharp a-p₂^sharp a
-- statement:
--   Let $k$ be a field, let $f\colon A\to\operatorname{Spec} k$ be a scheme over $k$ and let $L$ be a `RelativeGroupLaw` for $f$, that is, functorial multiplication, unit and inverse operations on the sets $\{\varphi\colon T\to A \mid \varphi\circ f=t\}$ of points of $A$ over a base morphism $t\colon T\to\operatorname{Spec} k$, satisfying associativity, both unit laws, left inverse law, and naturality of multiplication under change of $T$. Let $U_e$ be an open of $A$, and let $U'$ be an affine open of the fibre product $A\times_{\operatorname{Spec} k}A$ contained in the preimages of $U_e$ under the first projection, the second projection, and the multiplication $\mu$ of the two tautological points $p_1$ and $p_2$ of $A$ over $p_1\circ f$. Let $e_P\colon\operatorname{Spec} k\to U'$ be a section whose composites with $U'\hookrightarrow A\times_k A$ followed by either projection equal the unit point $L.\mathrm{one}(\mathrm{id})$. Let $M$ be a $k$-vector space and let $D$ be an element of [`Algebra.PointDerivations`](def/Algebra_PointDerivations.html#L9), i.e. a $k$-linear map $\Gamma(A\times_k A,U')\to M$ (the algebra structure being the one induced by $p_1\circ f$) satisfying $D(ab)=\mathrm{ev}(a)\cdot D(b)+\mathrm{ev}(b)\cdot D(a)$, where $\mathrm{ev}$ is evaluation at $e_P$. Then for every $a\in\Gamma(A,U_e)$ one has $D\bigl(\mu^\sharp a|_{U'}-p_1^\sharp a|_{U'}-p_2^\sharp a|_{U'}\bigr)=0$, the comorphism images being restricted to $U'$ along the three inclusions.
--
--   This is the statement that the differential of the group law at the unit is addition, $d\mu_{(e,e)}=dp_1+dp_2$ on $T_{(e,e)}(A\times A)=T_eA\oplus T_eA$, in the form of a relation satisfied by point derivations on an affine chart around $(e,e)$. It is used in the variant [`GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen`](thm.html#GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen), within the tangent-space analysis of schemes carrying a relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (Ue : A.Opens)
    (U' : (pullback f f).Opens) (hU' : IsAffineOpen U')
    (hU₁ : U' ≤ pullback.fst f f ⁻¹ᵁ Ue) (hU₂ : U' ≤ pullback.snd f f ⁻¹ᵁ Ue)
    (hUμ : U' ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ Ue)
    (eP : Spec (CommRingCat.of k) ⟶ (U' : Scheme.{u}))
    (heP₁ : eP ≫ U'.ι ≫ pullback.fst f f = (L.one (𝟙 _)).1) (heP₂ : eP ≫ U'.ι ≫ pullback.snd f f = (L.one (𝟙 _)).1)
    (M : Type u) [AddCommGroup M] [Module k M]
    (D : letI := algebraOfHom (pullback.fst f f ≫ f) U'
      ↥(Algebra.PointDerivations k Γ(pullback f f, U')
          ((U'.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) M))
    (a : Γ(A, Ue)) :
    D.1 (((pullback f f).presheaf.map (homOfLE hUμ).op).hom
            (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₁).op).hom (((pullback.fst f f).app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₂).op).hom (((pullback.snd f f).app Ue).hom a)) = 0 := by sorry
