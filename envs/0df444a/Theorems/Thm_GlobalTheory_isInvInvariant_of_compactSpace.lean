-- Prove2me | Theorems.Thm_GlobalTheory_isInvInvariant_of_compactSpace
-- name    : GlobalTheory.isInvInvariant_of_compactSpace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:06.474014+00:00
-- url     : https://prove2.me/theorems/64851a61-13f0-5987-b94d-b79bc8c5317c
-- title:
--   Global Theory: is Inv Invariant of compact Space
-- statement:
--   The Global Theory construction uses the is Inv Invariant of compact Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L53-L56

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

theorem GlobalTheory.isInvInvariant_of_compactSpace (μ : Measure K) [μ.IsHaarMeasure] :
    μ.IsInvInvariant := by sorry
