-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_ConeOne_cone_def
-- name    : GlobalTheory.HCXi.ConeOne.cone_def
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:01.15991+00:00
-- url     : https://prove2.me/theorems/b9211b32-4f44-5810-b3e9-8d958e0e9707
-- title:
--   Cone One: cone def
-- statement:
--   The Cone One construction uses the cone def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasurePosRank.lean#L51-L52

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

theorem GlobalTheory.HCXi.ConeOne.cone_def (k r' : ℕ) :
    coneMeas k r' = ((radMeas (2 * r' + k + 1)).prod (volume : Measure (HPar k r'))).map (par k r') := by sorry
