-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_existsUnique_primitive_param
-- name    : GlobalTheory.FormalCalc.existsUnique_primitive_param
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:33:51.897814+00:00
-- url     : https://prove2.me/theorems/ff7e1030-7979-43b9-90a3-1847fbfa15ab
-- title:
--   Formal Calc: exists Unique primitive param
-- statement:
--   The Formal Calc construction uses the exists Unique primitive param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L137-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L137-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ ι A : Type*} [CommRing A]
variable [Algebra ℚ A]

theorem GlobalTheory.FormalCalc.existsUnique_primitive_param {e : ι → σ} (he : Function.Injective e)
    (a : ι → MvPowerSeries σ A) (ha : ∀ i j, pderiv A (e i) (a j) = pderiv A (e j) (a i)) :
    ∃! f : MvPowerSeries σ A, (∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0) ∧
      ∀ i, pderiv A (e i) f = a i := by sorry
