-- Prove2me | Theorems.Thm_GlobalTheory_WittIntegrality_mem_of_mul_p_mem
-- name    : GlobalTheory.WittIntegrality.mem_of_mul_p_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:29.161386+00:00
-- url     : https://prove2.me/theorems/7896966d-3de7-46a4-b8dc-42c0b4ff8c47
-- title:
--   Witt Integrality: mem of mul p mem
-- statement:
--   The Witt Integrality construction uses the mem of mul p mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittMatrixCoeffMemOfFrobenius.lean#L55-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable [CharP C p]

theorem GlobalTheory.WittIntegrality.mem_of_mul_p_mem {x : WittVector p C} (hx : x * (p : WittVector p C) ∈ S A p) :
    x ∈ S A p := by sorry
