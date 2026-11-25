-- Prove2me | Theorems.Thm_GlobalTheory_Nef_isRat_of_hankel_eventually_zero
-- name    : GlobalTheory.Nef.isRat_of_hankel_eventually_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:02:02.016291+00:00
-- url     : https://prove2.me/theorems/6d55628b-ea71-4186-ac69-7f9a427f7d04
-- title:
--   Nef: is Rat of hankel eventually zero
-- statement:
--   The Nef construction uses the is Rat of hankel eventually zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L175-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.isRat_of_hankel_eventually_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ),
    (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by sorry
