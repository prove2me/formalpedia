-- Prove2me | Theorems.Thm_GlobalTheory_KTypeSteps_sqrt_nsq_eq
-- name    : GlobalTheory.KTypeSteps.sqrt_nsq_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:46:44.544927+00:00
-- url     : https://prove2.me/theorems/458f5bf3-244d-4265-bb4d-c2b51cf9d089
-- title:
--   KType Steps: sqrt nsq eq
-- statement:
--   The KType Steps construction uses the sqrt nsq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/KtypesWithinSteps.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/KtypesWithinSteps.lean#L10-L14

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

theorem GlobalTheory.KTypeSteps.sqrt_nsq_eq {n : ℕ} (v : Fin n → ℝ) :
    Real.sqrt (nsq v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by sorry
