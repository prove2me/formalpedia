-- Prove2me | Theorems.Thm_GlobalTheory_T_haar_measure_L_unit_smul_absK_sq
-- name    : GlobalTheory.T.haar_measure_L_unit_smul_absK_sq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:41:55.903849+00:00
-- url     : https://prove2.me/theorems/85ad9bf7-1276-4887-887c-c6897ef5dd53
-- title:
--   T: haar measure L unit smul abs K sq
-- statement:
--   The T construction uses the haar measure L unit smul abs K sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HaarMeasureLUnitSmulAbsKSqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HaarMeasureLUnitSmulAbsKSqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HaarMeasureLUnitSmulAbsKSq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HaarMeasureLUnitSmulAbsKSqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.haar_measure_L_unit_smul_absK_sq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ (c : A.Kˣ) (S : Set A.L), μ {y : A.L | ∃ z ∈ S, y = algebraMap A.K A.L (c : A.K) * z} = ENNReal.ofReal (A.absK (c : A.K) ^ 2) * μ S := by sorry
