-- Prove2me | Theorems.Thm_GlobalTheory_ConeCharCheck_exists_strictAnti
-- name    : GlobalTheory.ConeCharCheck.exists_strictAnti
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:02:39.741081+00:00
-- url     : https://prove2.me/theorems/67a60034-0a0f-4899-8c7e-df639702d194
-- title:
--   Cone Char Check: exists strict Anti
-- statement:
--   The Cone Char Check construction uses the exists strict Anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/DegenerateExamples/ExistsStrictAnti.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/DegenerateExamples/ExistsStrictAnti.lean#L11-L14

import Mathlib
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_DegenerateExamples_ExistsStrictAnti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ConeCharCheck

theorem GlobalTheory.ConeCharCheck.exists_strictAnti (r : ℕ) : ∃ a : Fin r → ℤ, StrictAnti a := by sorry
