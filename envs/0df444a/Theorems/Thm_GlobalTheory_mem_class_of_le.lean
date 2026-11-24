-- Prove2me | Theorems.Thm_GlobalTheory_mem_class_of_le
-- name    : GlobalTheory.mem_class_of_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:36.82521+00:00
-- url     : https://prove2.me/theorems/a65b3513-3b73-4f4b-a021-f9bbe84c3cf3
-- title:
--   Global Theory: mem class of le
-- statement:
--   The Global Theory construction uses the mem class of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TendstoTsumZeroOfEventuallyNotMemRange.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TendstoTsumZeroOfEventuallyNotMemRange.lean#L43-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Filter Topology
open GlobalTheory

theorem GlobalTheory.mem_class_of_le {X : Type} [AddCommGroup X] {n : ℕ} {α : ℕ → X}
    (hα : ∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) {z : X} {j k : ℕ} (hjk : j ≤ k)
    (hz : ∃ μ, z = α k + n ^ k • μ) : ∃ μ, z = α j + n ^ j • μ := by sorry
