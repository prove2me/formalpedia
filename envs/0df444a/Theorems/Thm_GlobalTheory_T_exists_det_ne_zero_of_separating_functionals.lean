-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_det_ne_zero_of_separating_functionals
-- name    : GlobalTheory.T.exists_det_ne_zero_of_separating_functionals
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:34:19.724852+00:00
-- url     : https://prove2.me/theorems/8b88b027-9469-4792-bd0a-5475486006f7
-- title:
--   T: exists det ne zero of separating functionals
-- statement:
--   The T construction uses the exists det ne zero of separating functionals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDetNeZeroOfRowsSeparatingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDetNeZeroOfRowsSeparatingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparating
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDetNeZeroOfRowsSeparatingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_det_ne_zero_of_separating_functionals : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by sorry
