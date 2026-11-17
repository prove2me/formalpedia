-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_division_fibre_point_equiv
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_division_fibre_point_equiv
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:40.0652+00:00
-- url     : https://prove2.me/theorems/836a34c0-d7f9-4bb0-9a7c-d6332748861b
-- title:
--   A division fibre represents the solutions of the corresponding multiplication equation
-- statement:
--   Let $L$ be a relative group law on $B/R$, let $S$ be a section, let $n∈ℕ$, and let $T→\operatorname{Spec}R$. The $T$-points of the pullback of $[n]:B→B$ along $S$ are naturally equivalent to the points $x∈B(T)$ satisfying $[n]x=S_T$: $$\operatorname{Hom}_R(T,[n]^{-1}(S))\;≃\;\{x∈B(T):[n]x=S_T\}.$$ The equivalence sends a pullback point to its projection to $B$. This is the representability statement for a division fibre.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

theorem GoodReductionJacobian.RelativeGroupLaw.exists_division_fibre_point_equiv
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ∃ e : SchemeHomOver t (pullback.snd (L.schemeNsmul n) S.1) ≃
        {x : SchemeHomOver t f // L.nsmul t n x =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) S},
      ∀ x, (e x).1.1 = x.1 ≫ pullback.fst (L.schemeNsmul n) S.1 := by sorry
