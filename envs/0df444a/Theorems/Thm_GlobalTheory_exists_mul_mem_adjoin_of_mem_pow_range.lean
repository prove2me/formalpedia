-- Prove2me | Theorems.Thm_GlobalTheory_exists_mul_mem_adjoin_of_mem_pow_range
-- name    : GlobalTheory.exists_mul_mem_adjoin_of_mem_pow_range
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:35:17.82489+00:00
-- url     : https://prove2.me/theorems/05a64b30-7752-47f1-b61a-28a53740940f
-- title:
--   Global Theory: exists mul mem adjoin of mem pow range
-- statement:
--   The Global Theory construction uses the exists mul mem adjoin of mem pow range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L61-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulMemAdjoinOfMemPowRange.lean#L61-L104

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

theorem GlobalTheory.exists_mul_mem_adjoin_of_mem_pow_range {K T : Type} [Field K] [CommRing T] [Algebra K T]
    {m : ℕ} (x : Fin m → T) (s : T)
    (hs : ∀ i, ∃ n : ℕ, s * x i ^ n ∈ Algebra.adjoin K (Set.range x)) :
    ∃ N : ℕ, ∀ t ∈ (Set.range x) ^ N, s * t ∈ Algebra.adjoin K (Set.range x) := by sorry
