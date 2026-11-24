-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsQuad_range_h90_le_normOne
-- name    : GlobalTheory.WeilM.IsQuad.range_h90_le_normOne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:53:55.422037+00:00
-- url     : https://prove2.me/theorems/b4eca7de-f9f0-4357-8451-b5bc3ac51d52
-- title:
--   Is Quad: range h90 le norm One
-- statement:
--   The Is Quad construction uses the range h90 le norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L237-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L237-L243

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
open GlobalTheory.WeilM.IsQuad
variable {ξ : E} (h : IsQuad c ξ)
include h

theorem GlobalTheory.WeilM.IsQuad.range_h90_le_normOne : (h90 c).range ≤ normOne c := by sorry
