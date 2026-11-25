-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_map
-- name    : GlobalTheory.HCXi.ConeOne.cone_map
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:43:35.806093+00:00
-- url     : https://prove2.me/theorems/602c8ed2-dab3-49ee-9340-ce97fe404877
-- title:
--   Cone One: cone map
-- statement:
--   The Cone One construction uses the cone map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L60-L71

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

theorem GlobalTheory.HCXi.ConeOne.cone_map (k r' : ℕ) (t : ℝ) (ht : 0 < t) :
    (coneMeas k r').map (fun v => (t : ℂ) • v) =
      ENNReal.ofReal ((t ^ (2 * (2 * r' + k + 1) + 2))⁻¹) • coneMeas k r' := by sorry
