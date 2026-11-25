-- Prove2me | Theorems.Thm_GlobalTheory_Nef_coeff_mul_of_coeff_lt_eq_zero
-- name    : GlobalTheory.Nef.coeff_mul_of_coeff_lt_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:43.151224+00:00
-- url     : https://prove2.me/theorems/0933db4b-9264-456d-af9e-5f334cf4209b
-- title:
--   Nef: coeff mul of coeff lt eq zero
-- statement:
--   The Nef construction uses the coeff mul of coeff lt eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomPowerSeriesEqOfRescale.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingHomPowerSeriesEqOfRescale.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingHomPowerSeriesEqOfRescale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.coeff_mul_of_coeff_lt_eq_zero {R : Type} [CommRing R] (φ δ : PowerSeries R) (j : ℕ)
    (h : ∀ i < j, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff j (φ * δ) = PowerSeries.constantCoeff φ * PowerSeries.coeff j δ := by sorry
