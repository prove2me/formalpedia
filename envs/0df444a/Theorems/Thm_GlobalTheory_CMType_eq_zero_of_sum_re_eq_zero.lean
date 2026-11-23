-- Prove2me | Theorems.Thm_GlobalTheory_CMType_eq_zero_of_sum_re_eq_zero
-- name    : GlobalTheory.CMType.eq_zero_of_sum_re_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:03.134093+00:00
-- url     : https://prove2.me/theorems/6b10d4aa-c851-4126-97de-c96c9eb1465a
-- title:
--   CMType: eq zero of sum re eq zero
-- statement:
--   The CMType construction uses the eq zero of sum re eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L119-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/MemIffConjugateNotMem.lean#L119-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.CMType
variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)

theorem GlobalTheory.CMType.eq_zero_of_sum_re_eq_zero (δ : Φ → ℂ)
    (h : ∀ a : 𝓞 E, ∑ τ : Φ, (τ.1 (a : E) * δ τ).re = 0) : δ = 0 := by sorry
