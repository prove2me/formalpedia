-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_smul_periodMap_of_orthogonal_ker
-- name    : GlobalTheory.AnArc.smul_periodMap_of_orthogonal_ker
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:10.974809+00:00
-- url     : https://prove2.me/theorems/c54c1220-7af2-4aa1-b4fe-dcbb162b08da
-- title:
--   An Arc: smul period Map of orthogonal ker
-- statement:
--   The An Arc construction uses the smul period Map of orthogonal ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L163-L166

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

theorem GlobalTheory.AnArc.smul_periodMap_of_orthogonal_ker {v : A.La} (h : ∀ v' : A.La, v'.y = 0 → A.EF v v' = 0) (s : ℂ) :
    (s • A.P0 v).2 = 0 ∧ ∀ v' : A.La, (s • A.P0 v).1 v'.y = -(s * A.EF v v') := by sorry
