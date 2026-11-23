-- Prove2me | Theorems.Thm_GlobalTheory_eq_smul_haarProb
-- name    : GlobalTheory.eq_smul_haarProb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:26.965561+00:00
-- url     : https://prove2.me/theorems/175e7cb8-4106-416b-9a4d-9cb3a42e58bc
-- title:
--   Global Theory: eq smul haar Prob
-- statement:
--   The Global Theory construction uses the eq smul haar Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L40-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {K}

theorem GlobalTheory.eq_smul_haarProb (μ : Measure K) [μ.IsHaarMeasure] :
    μ = μ Set.univ • haarProb K := by sorry
