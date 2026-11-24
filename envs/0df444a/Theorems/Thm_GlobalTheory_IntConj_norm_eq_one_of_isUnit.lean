-- Prove2me | Theorems.Thm_GlobalTheory_IntConj_norm_eq_one_of_isUnit
-- name    : GlobalTheory.IntConj.norm_eq_one_of_isUnit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:59.987688+00:00
-- url     : https://prove2.me/theorems/e1f58e0d-379f-4c48-a299-a278e4e25965
-- title:
--   Int Conj: norm eq one of is Unit
-- statement:
--   The Int Conj construction uses the norm eq one of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommutantMulIntegralConjugate.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCommutantMulIntegralConjugate.lean#L34-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorSemilocalOfCyclicVectorField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory GlobalTheory.IntConj

theorem GlobalTheory.IntConj.norm_eq_one_of_isUnit {E : Type} [NormedField E] [IsUltrametricDist E]
    {a : (NormedField.valuation (K := E)).valuationSubring} (ha : IsUnit a) : ‖(a : E)‖ = 1 := by sorry
