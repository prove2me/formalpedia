-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_orth_ker_iff_exists
-- name    : GlobalTheory.AnArc.orth_ker_iff_exists
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:28:58.214237+00:00
-- url     : https://prove2.me/theorems/5bd71326-a935-4631-bb5a-7b6ec96b5f64
-- title:
--   An Arc: orth ker iff exists
-- statement:
--   The An Arc construction uses the orth ker iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L145-L146

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

theorem GlobalTheory.AnArc.orth_ker_iff_exists (v : A.La) : (∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) ↔ ∃ n, v = La.mk 0 n 0 := by sorry
