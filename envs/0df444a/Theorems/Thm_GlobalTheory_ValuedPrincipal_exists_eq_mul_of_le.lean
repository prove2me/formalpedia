-- Prove2me | Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_eq_mul_of_le
-- name    : GlobalTheory.ValuedPrincipal.exists_eq_mul_of_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:50:25.593911+00:00
-- url     : https://prove2.me/theorems/fe8f54b0-1b36-4209-89c6-3c7f8482b95c
-- title:
--   Valued Principal: exists eq mul of le
-- statement:
--   The Valued Principal construction uses the exists eq mul of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L113-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExistsLeastOfDiscrete.lean#L113-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem GlobalTheory.ValuedPrincipal.exists_eq_mul_of_le {t a : F} (ht : t ≠ 0) (h : v t ≤ v a) :
    ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t := by sorry
