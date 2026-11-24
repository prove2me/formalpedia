-- Prove2me | Theorems.Thm_GlobalTheory_JR_TruncInt_isLocallyConstant_indicator
-- name    : GlobalTheory.JR.TruncInt.isLocallyConstant_indicator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:55.771808+00:00
-- url     : https://prove2.me/theorems/8b3fe66c-525c-430d-a524-83c336d1cbf1
-- title:
--   Trunc Int: is Locally Constant indicator
-- statement:
--   The Trunc Int construction uses the is Locally Constant indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TruncatedIntegralEqVolMulOrbitalIntegral.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TruncatedIntegralEqVolMulOrbitalIntegral.lean#L22-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedIntegralEqVolMulOrbitalIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.TruncInt
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.TruncInt.isLocallyConstant_indicator {X : Type} [TopologicalSpace X] {W : Set X} (hW : IsClopen W) (c : ℂ) :
    IsLocallyConstant (W.indicator fun _ => c) := by sorry
