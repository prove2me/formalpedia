-- Prove2me | Theorems.Thm_GlobalTheory_AnArc_hermForm_HwMat
-- name    : GlobalTheory.AnArc.hermForm_HwMat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:29.694911+00:00
-- url     : https://prove2.me/theorems/e54ff4cb-86d6-46b4-9b9e-5c6818f7e52b
-- title:
--   An Arc: herm Form Hw Mat
-- statement:
--   The An Arc construction uses the herm Form Hw Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L430-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/TorusProjPeriodZeroEqReal.lean#L430-L440

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem GlobalTheory.AnArc.hermForm_HwMat (w : ℂ) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (v v' : A.V) :
    hermForm (A.HwMat w h) (h v) (h v') = A.Hw w v v' := by sorry
