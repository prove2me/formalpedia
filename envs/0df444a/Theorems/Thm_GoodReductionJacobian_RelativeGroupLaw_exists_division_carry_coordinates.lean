-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_coordinates
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_coordinates
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:55.574248+00:00
-- url     : https://prove2.me/theorems/18620e44-e5d9-43ab-a4f5-4e8be7fb3d68
-- title:
--   The $71$-division fibres carry a commutative law with the integral carry formula
-- statement:
--   Let $R$ be a commutative ring, let $L$ be a commutative relative group law on $B→\operatorname{Spec}R$, and let $S$ be a section. For $a∈ℤ/71ℤ$, let $X_a=[71]^{-1}([a]S)$ and let $X=\coprod_aX_a$. There is a commutative relative group law $H$ on $X$ such that, whenever $x∈X_a$ and $y∈X_b$ project to prescribed points $p_x,p_y∈B(T)$, their product lies in $X_{a+b}$ and projects to $$p_xp_y\,[S_T]^{-\lfloor(a_{val}+b_{val})/71\rfloor}.$$ This is the coordinate-level carry law needed to model the Kummer extension by a finite group scheme.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibreProjection

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

theorem GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_coordinates
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ H : RelativeGroupLaw R (Sigma.desc g), H.IsCommutative ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ZMod 71)
        (x : SchemeHomOver t (g a)) (y : SchemeHomOver t (g b))
        (px py : SchemeHomOver t f),
        x.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1 = px.1 →
        y.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1 = py.1 →
        ∃ z : SchemeHomOver t (g (a + b)),
          (H.mul t ⟨x.1 ≫ Sigma.ι X a, by rw [Category.assoc, Sigma.ι_desc]; exact x.2⟩
            ⟨y.1 ≫ Sigma.ι X b, by rw [Category.assoc, Sigma.ι_desc]; exact y.2⟩).1 =
              z.1 ≫ Sigma.ι X (a + b) ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71)
              (L.nsmul (𝟙 _) (a + b).val S).1 =
            (L.mul t (L.mul t px py)
              (L.inv t (L.nsmul t ((a.val + b.val) / 71)
                (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S)))).1 := by sorry
