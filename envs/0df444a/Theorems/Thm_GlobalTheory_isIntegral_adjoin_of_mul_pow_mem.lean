-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_adjoin_of_mul_pow_mem
-- name    : GlobalTheory.isIntegral_adjoin_of_mul_pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:45.035056+00:00
-- url     : https://prove2.me/theorems/c386e12c-d6a2-448c-a8b3-c1f009d9931b
-- title:
--   Global Theory: is Integral adjoin of mul pow mem
-- statement:
--   The Global Theory construction uses the is Integral adjoin of mul pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L106-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L106-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulMemAdjoinOfMemPowRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
open scoped Pointwise

theorem GlobalTheory.isIntegral_adjoin_of_mul_pow_mem :
    (∀ (K T : Type) [Field K] [CommRing T] [IsDomain T] [Algebra K T] (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] (m : ℕ) (x : Fin m → T), (∀ i, x i ∈ 𝒜 1) → (∃ i, x i ≠ 0) → ∀ (d : ℕ), ∀ s ∈ 𝒜 d, (∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) → IsIntegral (Algebra.adjoin K (Set.range x)) s) := by sorry
