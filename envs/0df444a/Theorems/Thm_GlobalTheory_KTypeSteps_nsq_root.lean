-- Prove2me | Theorems.Thm_GlobalTheory_KTypeSteps_nsq_root
-- name    : GlobalTheory.KTypeSteps.nsq_root
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:09.069797+00:00
-- url     : https://prove2.me/theorems/8473be86-0ae6-4a22-8f6d-12c14ffe77e8
-- title:
--   KType Steps: nsq root
-- statement:
--   The KType Steps construction uses the nsq root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/KtypesWithinSteps.lean#L21-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/KtypesWithinSteps.lean#L21-L33

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

theorem GlobalTheory.KTypeSteps.nsq_root {n : ℕ} {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by sorry
