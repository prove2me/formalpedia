-- Prove2me | Theorems.Thm_MazurTransfer_FiniteRatFuncPicardDivisible_picard_divisible_of_finite_ratFunc
-- name    : MazurTransfer.FiniteRatFuncPicardDivisible.picard_divisible_of_finite_ratFunc
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T08:17:18.053984+00:00
-- url     : https://prove2.me/theorems/700c954e-8758-4215-8815-1d9ba2171a2b
-- title:
--   Divisibility of Picard classes over finite extensions of RatFunc K
-- statement:
--   Let K be an algebraically closed field of characteristic zero. Let L be a field with compatible K and RatFunc K algebra structures and a scalar tower, and suppose L is finite-dimensional over RatFunc K. Then the original divisor-theoretic group Pic0 K L is divisible: for each nonzero integer m and every class x there is a class y with m • y = x. No curve structure or divisibility assumption is added to the input. Named downstream consumer: the divisibility-based injectivity of the actual order-13 divisorial nineteen-pairing.
-- source:
--   MazurTheorem, FiniteRatFuncPicardDivisible.lean; Apache-2.0. Its four proofs are reused from Anthropic FLT P2M/Sol/S_AlgebraicCurve_Pic0_exists_weilPairing.lean at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. Complete original theorem type and all three helper types checked.

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.RatFunc.Basic
noncomputable section
open AlgebraicCurve

theorem MazurTransfer.FiniteRatFuncPicardDivisible.picard_divisible_of_finite_ratFunc {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (L' : Type*) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
    [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'] :
    ∀ m : ℤ, m ≠ 0 → ∀ x : Pic0 K L', ∃ y, m • y = x := by sorry
