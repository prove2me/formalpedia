-- Prove2me | Theorems.Thm_GlobalTheory_isMulRightInvariant_of_compactSpace
-- name    : GlobalTheory.isMulRightInvariant_of_compactSpace
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:10.906309+00:00
-- url     : https://prove2.me/theorems/a65e05f6-1d61-4d8a-96b7-b9faca8ff63f
-- title:
--   Global Theory: is Mul Right Invariant of compact Space
-- statement:
--   The Global Theory construction uses the is Mul Right Invariant of compact Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L49-L51

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

theorem GlobalTheory.isMulRightInvariant_of_compactSpace (μ : Measure K) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by sorry
