-- Prove2me | Theorems.Thm_MazurTransfer_original_nineteen_roots_cyclotomic_power
-- name    : MazurTransfer.original_nineteen_roots_cyclotomic_power
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T18:49:42.500005+00:00
-- url     : https://prove2.me/theorems/cfe5afb1-7672-4649-9360-1e4cfcdafedf
-- statement:
--   The same natural cyclotomic exponent describes the action on every original literal nineteenth root and the previously fixed roots representation. Nineteen annihilates that same additive roots module. On the original character kernel the inverse-character twist has exactly that same exponent action, in particular for the previously fixed conjugate-pi reflected character. Every original field, characteristic-zero, Galois, algebraic-closure, primitive-root and kernel hypothesis is retained exactly. Named downstream consumer: cyclotomic Hopf classification and descent for the same selected arithmetic character quotients at nineteen.

import Definitions.Def_MazurTransfer_OriginalNineteenRootsCyclotomicPowerData20261020
noncomputable section
open MazurTransfer.NineteenRootsGaloisRepresentation MazurTransfer.RepresentationCharacterTwist
open MazurTransfer.Order13ActualOrderedCharacterContinuousH1 MazurTransfer.Order13ActualCyclotomicThirteenKernelCharacter
open MazurTransfer.NineteenRootsCyclotomicPower
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instFactPrimeOfNatNat_nineteenRootsCyclotomicPower
attribute [local instance] MazurTransfer.NineteenRootsCyclotomicPower.instModuleZModOfNatNatAdditiveSubtypeUnitsMemSubgroupRoots_nineteenRootsCyclotomicPower

theorem MazurTransfer.original_nineteen_roots_cyclotomic_power : (∀ (K : Type) [Field K] [CharZero K] , ∀ (σ : K ≃ₐ[ℚ] K) (ζ : K) (hζ : ζ ^ 19 = 1),
σ ζ = ζ ^ exponent K σ) ∧ (∀ (K : Type) [Field K] [CharZero K] , ∀ (σ : K ≃ₐ[ℚ] K) (m : Additive (Roots K)),
rootsRepresentation K σ m = exponent K σ • m) ∧ (∀ (K : Type) [Field K] [CharZero K] , ∀ (m : Additive (Roots K)),
19 • m = 0) ∧ (∀ (K : Type) [Field K] [CharZero K] , ∀ (χ : (K ≃ₐ[ℚ] K) →* (ZMod 19)ˣ) (σ : K ≃ₐ[ℚ] K) (hχ : χ σ = 1)
    (m : Additive (Roots K)),
twist χ⁻¹ (rootsRepresentation K) σ m = exponent K σ • m) ∧ (∀ (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] [IsAlgClosed K] , ∀ (z : K) (hz : IsPrimitiveRoot z 13) (σ : K ≃ₐ[ℚ] K)
    (hχ : piConjugateReflectedCharacter K z hz σ = 1) (m : Additive (Roots K)),
twistedRootsRepresentation K z hz σ m = exponent K σ • m) := by sorry
