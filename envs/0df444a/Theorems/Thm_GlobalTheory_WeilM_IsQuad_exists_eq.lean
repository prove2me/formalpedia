-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsQuad_exists_eq
-- name    : GlobalTheory.WeilM.IsQuad.exists_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:05.544514+00:00
-- url     : https://prove2.me/theorems/f7e43386-9c09-41b4-afd2-98e410d48380
-- title:
--   Is Quad: exists eq
-- statement:
--   The Is Quad construction uses the exists eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L222-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L222-L225

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

theorem GlobalTheory.WeilM.IsQuad.exists_eq (z : E) : ∃ a b : R, z = algebraMap R E a + algebraMap R E b * ξ := by sorry
