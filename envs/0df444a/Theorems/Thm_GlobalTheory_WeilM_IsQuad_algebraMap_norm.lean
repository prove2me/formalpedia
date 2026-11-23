-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsQuad_algebraMap_norm
-- name    : GlobalTheory.WeilM.IsQuad.algebraMap_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:38.955109+00:00
-- url     : https://prove2.me/theorems/487a3964-da69-4c42-8420-fe514248cc33
-- title:
--   Is Quad: algebra Map norm
-- statement:
--   The Is Quad construction uses the algebra Map norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L270-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L270-L281

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
variable [Invertible (2 : R)]

theorem GlobalTheory.WeilM.IsQuad.algebraMap_norm (z : E) : algebraMap R E (Algebra.norm R z) = z * c z := by sorry
