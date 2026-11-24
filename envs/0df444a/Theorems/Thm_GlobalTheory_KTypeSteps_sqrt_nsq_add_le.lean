-- Prove2me | Theorems.Thm_GlobalTheory_KTypeSteps_sqrt_nsq_add_le
-- name    : GlobalTheory.KTypeSteps.sqrt_nsq_add_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:47:36.413608+00:00
-- url     : https://prove2.me/theorems/fe5c4730-1612-4026-a9e2-58f06bf281fa
-- title:
--   KType Steps: sqrt nsq add le
-- statement:
--   The KType Steps construction uses the sqrt nsq add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/KtypesWithinSteps.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/KtypesWithinSteps.lean#L16-L19

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_KtypesWithinSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.KTypeSteps

theorem GlobalTheory.KTypeSteps.sqrt_nsq_add_le {n : ℕ} (v w : Fin n → ℝ) :
    Real.sqrt (nsq (v + w)) ≤ Real.sqrt (nsq v) + Real.sqrt (nsq w) := by sorry
