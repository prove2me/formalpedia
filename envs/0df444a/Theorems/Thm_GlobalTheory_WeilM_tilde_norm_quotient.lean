-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_tilde_norm_quotient
-- name    : GlobalTheory.WeilM.tilde_norm_quotient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:54.779673+00:00
-- url     : https://prove2.me/theorems/a8ac9d5a-37d1-4faa-a722-48355c042184
-- title:
--   Weil M: tilde norm quotient
-- statement:
--   The Weil M construction uses the tilde norm quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L198-L200

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

theorem GlobalTheory.WeilM.tilde_norm_quotient (χ : Eˣ →* Circle) (hχ : ∀ z : Eˣ, c z = z → χ z = 1) (z : Eˣ) :
    tilde c χ hχ ⟨h90 c z, z, rfl⟩ = χ z := by sorry
