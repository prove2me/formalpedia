-- Prove2me | Theorems.Thm_GlobalTheory_exists_det_ne_zero_of_rows_separating
-- name    : GlobalTheory.exists_det_ne_zero_of_rows_separating
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:35.805665+00:00
-- url     : https://prove2.me/theorems/a389cfd1-8972-4e22-a4d6-53455d2426b6
-- title:
--   Global Theory: exists det ne zero of rows separating
-- statement:
--   The Global Theory construction uses the exists det ne zero of rows separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDetNeZeroOfRowsSeparating.lean#L6-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDetNeZeroOfRowsSeparating.lean#L6-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparating
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_det_ne_zero_of_rows_separating :
    ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K),
      (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) →
      ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by sorry
