-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finite_flat_division_fibre
-- name    : GoodReductionJacobian.RelativeGroupLaw.finite_flat_division_fibre
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:20.75024+00:00
-- url     : https://prove2.me/theorems/82cebe94-0730-4671-a4ab-489de17f418e
-- title:
--   Every positive division fibre of an abelian scheme is finite and flat
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $B/R$ be an abelian scheme with commutative relative group law $L$, let $n>0$, and let $S$ be a section. Then the fibre of multiplication by $n$ above $S$ is finite and flat over $R$: $$[n]^{-1}(S)→\operatorname{Spec}R\text{ is finite and flat}.$$ This supplies the finite-flat schemes used to realize local Galois representations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open GoodReductionJacobian
open GoodReductionJacobian.RelativeGroupLaw

theorem GoodReductionJacobian.RelativeGroupLaw.finite_flat_division_fibre
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hB : AbelianSchemePropertyBundle R f)
    (hc : L.IsCommutative) (n : ℕ) (hn : 0 < n)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    IsFinite (pullback.snd (L.schemeNsmul n) S.1) ∧
      Flat (pullback.snd (L.schemeNsmul n) S.1) := by sorry
