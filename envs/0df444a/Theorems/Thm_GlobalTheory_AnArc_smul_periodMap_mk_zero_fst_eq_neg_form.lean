-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_smul_periodMap_mk_zero_fst_eq_neg_form
-- name    : GlobalTheory.AnArc.smul_periodMap_mk_zero_fst_eq_neg_form
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:28:52.505701+00:00
-- url     : https://prove2.me/theorems/13deb443-cdf4-44dd-a574-2b8e0552188d
-- title:
--   An Arc: smul period Map mk zero fst eq neg form
-- statement:
--   The An Arc construction uses the smul period Map mk zero fst eq neg form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L148-L150

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

theorem GlobalTheory.AnArc.smul_periodMap_mk_zero_fst_eq_neg_form (s : ℂ) (n : A.X →+ ℤ) (v' : A.La) :
    (s • A.P0 (La.mk 0 n 0)).1 v'.y = -(s * A.EF (La.mk 0 n 0) v') := by sorry
