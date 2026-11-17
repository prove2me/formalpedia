-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_unit
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_unit
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:40.593799+00:00
-- url     : https://prove2.me/theorems/ddb16310-3f32-4ee0-9f66-e5c9686dda90
-- title:
--   The division-fibre coproduct has a unit section in the zero component
-- statement:
--   Let $L$ be a relative group law on $B/R$, let $S$ be a section, and put $X_a=[71]^{-1}([a]S)$ and $X=\coprod_aX_a$. There are a section $η$ of $X/R$ and a section $z$ of $X_0/R$ such that $η$ is the inclusion of $z$ and $$π(z)=1_B.$$ This supplies the identity element for the division-carry group scheme.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

theorem GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_unit
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ (η : SchemeHomOver (𝟙 _) (Sigma.desc g))
        (z : SchemeHomOver (𝟙 _) (g 0)),
      η.1 = z.1 ≫ Sigma.ι X 0 ∧
      z.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) (0 : ZMod 71).val S).1 =
        (L.one (𝟙 _)).1 := by sorry
