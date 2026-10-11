-- Prove2me | Theorems.Thm_MazurTransfer_relative_group_norm_factors_finite_of_invertible_scalar
-- name    : MazurTransfer.relative_group_norm_factors_finite_of_invertible_scalar
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T18:14:21.756109+00:00
-- url     : https://prove2.me/theorems/e141552a-2248-4ded-8790-c88193c7753d
-- title:
--   Invertible scalar norm factorizations on proper commutative group schemes have finite factors
-- statement:
--   Let A be a proper commutative group scheme over a local commutative ring R. If the two composites of R-endomorphisms φ and ψ equal multiplication by an integer n that is a unit in R, then φ and ψ are finite morphisms. This criterion is used for the two actual norm-nineteen endomorphisms of the rational order-thirteen Picard scheme. Surjectivity, flatness and the degrees of the factors are separate statements.
-- source:
--   Owned MazurTheorem integration argument using Mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474 and the complete original Apache-2.0 Anthropic FLT relative-group formal-unramifiedness theorem, pin 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.lean

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem MazurTransfer.relative_group_norm_factors_finite_of_invertible_scalar
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (G : RelativeGroupLaw R f) (hcomm : G.IsCommutative)
    (n : ℕ) (hn : IsUnit (n : R))
    (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    (hφψ : φ ≫ ψ = G.schemeNsmul n) (hψφ : ψ ≫ φ = G.schemeNsmul n) :
    IsFinite φ ∧ IsFinite ψ := by sorry
