-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeOne_radMeas_map
-- name    : GlobalTheory.HCXi.ConeOne.radMeas_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:52.399668+00:00
-- url     : https://prove2.me/theorems/270d5485-799b-5757-873f-05b0930e8bc4
-- title:
--   Cone One: rad Meas map
-- statement:
--   The Cone One construction uses the rad Meas map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L18-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L18-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8

theorem GlobalTheory.HCXi.ConeOne.radMeas_map (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (radMeas N).map (fun c => (t : ℂ) * c) = ENNReal.ofReal ((t ^ (2 * N + 2))⁻¹) • radMeas N := by sorry
