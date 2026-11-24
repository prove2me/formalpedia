-- Prove2me | Theorems.Thm_GlobalTheory_EntrySumMulBound_entrySum_mul_le
-- name    : GlobalTheory.EntrySumMulBound.entrySum_mul_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:17.738327+00:00
-- url     : https://prove2.me/theorems/9d93d4b6-f64e-42a1-bac4-88fefca987a2
-- title:
--   Entry Sum Mul Bound: entry Sum mul le
-- statement:
--   The Entry Sum Mul Bound construction uses the entry Sum mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EntrySumMulLe.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EntrySumMulLe.lean#L5-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EntrySumMulLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EntrySumMulBound

theorem GlobalTheory.EntrySumMulBound.entrySum_mul_le :
    (let d1 : {n : Type} → [Fintype n] → Matrix n n ℂ → ℝ := @(fun {n : Type} [Fintype n] (M : Matrix n n ℂ) ↦ ∑ i : n, ∑ j : n, ‖M i j‖); ∀ {n : Type} [inst : Fintype n] (A B : Matrix n n ℂ), d1 (A * B) ≤ d1 A * d1 B) := by sorry
