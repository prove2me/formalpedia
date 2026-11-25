-- Prove2me | Theorems.Thm_GlobalTheory_SideCompare_decGap_of_cube
-- name    : GlobalTheory.SideCompare.decGap_of_cube
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:26.967708+00:00
-- url     : https://prove2.me/theorems/f152b570-b497-487e-a76e-fb0ab207316e
-- title:
--   Side Compare: dec Gap of cube
-- statement:
--   The Side Compare construction uses the dec Gap of cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DecSmoothAtGapOfDecSmooth.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DecSmoothAtGapOfDecSmooth.lean#L38-L43

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

theorem GlobalTheory.SideCompare.decGap_of_cube (k r : ℕ) (h : ℝ) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) : DecGap k r h := by sorry
