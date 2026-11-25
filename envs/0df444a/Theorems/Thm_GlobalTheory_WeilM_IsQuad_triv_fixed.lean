-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsQuad_triv_fixed
-- name    : GlobalTheory.WeilM.IsQuad.triv_fixed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:36.006894+00:00
-- url     : https://prove2.me/theorems/dffd7ccb-376a-5504-ae78-8b4001dbdc5c
-- title:
--   Is Quad: triv fixed
-- statement:
--   The Is Quad construction uses the triv fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L265-L268

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

theorem GlobalTheory.WeilM.IsQuad.triv_fixed {χ : Eˣ →* Circle} (hχ : ∀ a : Rˣ, χ (Units.map (algebraMap R E : R →* E) a) = 1) (z : Eˣ)
    (hz : c z = z) : χ z = 1 := by sorry
