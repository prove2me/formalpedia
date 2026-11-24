-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_pow_range_of_mem_adjoin
-- name    : GlobalTheory.mem_span_pow_range_of_mem_adjoin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:10:57.129169+00:00
-- url     : https://prove2.me/theorems/f3f0d7db-eaba-42ee-b4f4-8b64cd77de05
-- title:
--   Global Theory: mem span pow range of mem adjoin
-- statement:
--   The Global Theory construction uses the mem span pow range of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L26-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L26-L59

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

theorem GlobalTheory.mem_span_pow_range_of_mem_adjoin {K T : Type} [Field K] [CommRing T] [Algebra K T]
    (𝒜 : ℕ → Submodule K T) [GradedAlgebra 𝒜] {m : ℕ} (x : Fin m → T) (hx : ∀ i, x i ∈ 𝒜 1)
    (k : ℕ) (t : T) (ht : t ∈ Algebra.adjoin K (Set.range x)) (htk : t ∈ 𝒜 k) :
    t ∈ Submodule.span K ((Set.range x) ^ k) := by sorry
