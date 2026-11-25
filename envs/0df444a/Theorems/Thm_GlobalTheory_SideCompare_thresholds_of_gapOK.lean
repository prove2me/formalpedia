-- Prove2me | Theorems.Thm_GlobalTheory_SideCompare_thresholds_of_gapOK
-- name    : GlobalTheory.SideCompare.thresholds_of_gapOK
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:01:36.448208+00:00
-- url     : https://prove2.me/theorems/ead96289-7a14-4ba1-be8c-ab1925fe29eb
-- title:
--   Side Compare: thresholds of gap OK
-- statement:
--   The Side Compare construction uses the thresholds of gap OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DecSmoothAtGapOfDecSmooth.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DecSmoothAtGapOfDecSmooth.lean#L45-L54

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_LieMatrixVectors
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DecSmoothAtGapOfDecSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SideCompare
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
open PI.BesselPeriodGGP (IsHaarOn IsQuotMeas)
open Formalism.FourierDecayAlt GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap (Mat decExp decConst dimV dimN thrG thrS thrSS propExp DecGap Size Thresholds muS mulP IsSide
  IsSideNormalised KFinDecay wordSeminorm DecKFin DecSmooth)

theorem GlobalTheory.SideCompare.thresholds_of_gapOK (k r : ℕ) (h : ℝ) (hg : ThreeDimData.GapOK k r h) :
    DecGap k r h ∧ Thresholds k r (decExp r h) ∧ Thresholds k r (decExp r h - 1) := by sorry
