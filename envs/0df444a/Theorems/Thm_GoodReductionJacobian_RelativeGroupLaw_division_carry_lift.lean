-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_division_carry_lift
-- name    : GoodReductionJacobian.RelativeGroupLaw.division_carry_lift
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:40.375444+00:00
-- url     : https://prove2.me/theorems/c7a5c2e3-431c-42a3-87ab-77f4371cd2b7
-- title:
--   Products of division points lift with the quotient-and-remainder carry
-- statement:
--   Let $L$ be a commutative relative group law over a commutative ring $R$, let $S$ be a section, and let $T→\operatorname{Spec}R$. For natural numbers $n,a,b$, write $s=S_T$. If $x,y∈B(T)$ satisfy $x^n=s^a$ and $y^n=s^b$, then there exists a point $z$ in the fibre of $[n]$ above $[(a+b)\bmod n]S$ whose projection is $$π(z)=xy\,s^{-\lfloor(a+b)/n\rfloor}.$$ This is the basic lift implementing the carry term in the division-fibre multiplication.
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

theorem GoodReductionJacobian.RelativeGroupLaw.division_carry_lift
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n a b : ℕ) :
    letI := L.pointCommGroup hc t
    let s := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S
    ∀ x y : SchemeHomOver t f, x ^ n = s ^ a → y ^ n = s ^ b →
      ∃ z : SchemeHomOver t
          (pullback.snd (L.schemeNsmul n)
            (L.nsmul (𝟙 (Spec (CommRingCat.of R))) ((a + b) % n) S).1),
        z.1 ≫ pullback.fst (L.schemeNsmul n)
            (L.nsmul (𝟙 (Spec (CommRingCat.of R))) ((a + b) % n) S).1 =
          (x * y / s ^ ((a + b) / n)).1 := by sorry
