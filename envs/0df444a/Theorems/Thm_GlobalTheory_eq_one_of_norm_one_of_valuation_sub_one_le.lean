-- Prove2me | Theorems.Thm_GlobalTheory_eq_one_of_norm_one_of_valuation_sub_one_le
-- name    : GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:17:53.273937+00:00
-- url     : https://prove2.me/theorems/48526cb0-3736-46c3-90cb-fdcefbe04261
-- title:
--   Global Theory: eq one of norm one of valuation sub one le
-- statement:
--   The Global Theory construction uses the eq one of norm one of valuation sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqOneOfNormOneValuationSubOneSmall.lean#L15-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqOneOfNormOneValuationSubOneSmall.lean#L15-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqOneOfNormOneValuationSubOneSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.eq_one_of_norm_one_of_valuation_sub_one_le (E : Type) [Field E] [NumberField E] (ε : E)
    (w : HeightOneSpectrum (𝓞 E)) (K : ℕ) (hK : Module.finrank ℚ E < K)
    (hint : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1)
    (habs : ∀ φ : E →+* ℂ, ‖φ ε‖ = 1)
    (hw : w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ))) : ε = 1 := by sorry
