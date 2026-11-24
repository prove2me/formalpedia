-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_weak_approx_unit_finite_place
-- name    : GlobalTheory.T.exists_weak_approx_unit_finite_place
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:28.244983+00:00
-- url     : https://prove2.me/theorems/b0483c23-4343-4954-9913-3414fd080e5f
-- title:
--   T: exists weak approx unit finite place
-- statement:
--   The T construction uses the exists weak approx unit finite place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsWeakApproxUnitFinitePlaceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ExistsWeakApproxUnitFinitePlaceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsWeakApproxUnitFinitePlace
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsWeakApproxUnitFinitePlaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_weak_approx_unit_finite_place : ∀ (E : Type) [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℕ), ∃ y : E, y ≠ 0 ∧ Valued.v ((y : w.adicCompletion E) * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ ∀ v ∈ S, v ≠ w → v.valuation E (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by sorry
