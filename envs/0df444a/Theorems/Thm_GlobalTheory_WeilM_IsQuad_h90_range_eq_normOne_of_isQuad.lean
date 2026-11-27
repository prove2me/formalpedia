-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsQuad_h90_range_eq_normOne_of_isQuad
-- name    : GlobalTheory.WeilM.IsQuad.h90_range_eq_normOne_of_isQuad
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:11.777353+00:00
-- url     : https://prove2.me/theorems/e1aa3df9-c1da-56df-ac9a-ba8ae6ff7333
-- title:
--   Is Quad: h90 range eq norm One of is Quad
-- statement:
--   The Is Quad construction uses the h90 range eq norm One of is Quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L285-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L285-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}

theorem GlobalTheory.WeilM.IsQuad.h90_range_eq_normOne_of_isQuad {R : Type} [Field R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {ξ : E} (h : IsQuad c ξ) : (h90 c).range = normOne c := by sorry
