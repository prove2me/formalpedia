-- Prove2me | Theorems.Thm_GlobalTheory_mem_graded_of_mem_pow_range
-- name    : GlobalTheory.mem_graded_of_mem_pow_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:21.969334+00:00
-- url     : https://prove2.me/theorems/afdfbfc7-e424-4f85-99e6-a0227ede4d34
-- title:
--   Global Theory: mem graded of mem pow range
-- statement:
--   The Global Theory construction uses the mem graded of mem pow range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L10-L24

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

theorem GlobalTheory.mem_graded_of_mem_pow_range {K T : Type} [Field K] [CommRing T] [Algebra K T]
    (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] {m : ℕ} (x : Fin m → T) (hx : ∀ i, x i ∈ 𝒜 1) :
    ∀ (k : ℕ), ∀ t ∈ (Set.range x) ^ k, t ∈ 𝒜 k := by sorry
