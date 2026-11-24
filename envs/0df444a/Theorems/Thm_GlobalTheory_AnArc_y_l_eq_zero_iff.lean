-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_y_l_eq_zero_iff
-- name    : GlobalTheory.AnArc.y_l_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:53.516069+00:00
-- url     : https://prove2.me/theorems/516995d0-58ba-43bf-8edc-b16412dd924a
-- title:
--   An Arc: y l eq zero iff
-- statement:
--   The An Arc construction uses the y l eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L142-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L142-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.y_l_eq_zero_iff (v : A.La) : v.y = 0 ∧ v.l = 0 ↔ ∃ n, v = La.mk 0 n 0 := by sorry
