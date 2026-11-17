-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_carry_multiplication
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_multiplication
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:51.82246+00:00
-- url     : https://prove2.me/theorems/e1796fd0-2f16-40b5-a5de-32a9bb250fde
-- title:
--   The division-fibre coproduct admits a multiplication morphism with carry
-- statement:
--   Let $L$ be a commutative relative group law on $B/R$ and let $S$ be a section. For $X_a=[71]^{-1}([a]S)$ and $X=\coprod_aX_a$, there exists a multiplication morphism $μ:X×_RX→X$. On the component $X_a×_RX_b$, it factors through $X_{a+b}$ and, for the universal projected points $x,y$, the resulting point $z$ satisfies $$π(z)=xy\,[S]^{-\lfloor(a_{val}+b_{val})/71\rfloor}.$$ This gives the scheme-level multiplication underlying the division-carry group law.
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

theorem GoodReductionJacobian.RelativeGroupLaw.exists_division_carry_multiplication
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    let X : ZMod 71 → Scheme.{0} := fun a =>
      pullback (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    let g : ∀ a, X a ⟶ Spec (CommRingCat.of R) := fun a =>
      pullback.snd (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1
    ∃ μ : SchemeHomOver
        (pullback.fst (Sigma.desc g) (Sigma.desc g) ≫ Sigma.desc g) (Sigma.desc g),
      ∀ a b : ZMod 71,
        let t := pullback.fst (g a) (g b) ≫ g a
        letI := L.pointCommGroup hc t
        ∃ (x y : SchemeHomOver t f) (z : SchemeHomOver t (g (a + b))),
          x.1 = pullback.fst (g a) (g b) ≫
            pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) a.val S).1 ∧
          y.1 = pullback.snd (g a) (g b) ≫
            pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) b.val S).1 ∧
          pullback.map (g a) (g b) (Sigma.desc g) (Sigma.desc g)
              (Sigma.ι X a) (Sigma.ι X b) (𝟙 _) (by simp) (by simp) ≫ μ.1 =
            z.1 ≫ Sigma.ι X (a + b) ∧
          z.1 ≫ pullback.fst (L.schemeNsmul 71) (L.nsmul (𝟙 _) (a + b).val S).1 =
            (x * y / (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S) ^
              ((a.val + b.val) / 71)).1 := by sorry
