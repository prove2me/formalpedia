-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsTilde_unique
-- name    : GlobalTheory.WeilM.IsTilde.unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:57.783838+00:00
-- url     : https://prove2.me/theorems/4e57632f-1400-403d-8e25-35852b04162b
-- title:
--   Is Tilde: unique
-- statement:
--   The Is Tilde construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L211-L215

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

theorem GlobalTheory.WeilM.IsTilde.unique {χ : Eˣ →* Circle} (hχ : ∀ z : Eˣ, c z = z → χ z = 1) {u : Eˣ} {t t' : Circle}
    (h : IsTilde c χ u t) (h' : IsTilde c χ u t') : t = t' := by sorry
