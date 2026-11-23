-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_ext_of_pderiv_of_coeff
-- name    : GlobalTheory.FormalCalc.ext_of_pderiv_of_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:32.334592+00:00
-- url     : https://prove2.me/theorems/4b1adb25-c966-4493-9ee5-2b10a02b821b
-- title:
--   Formal Calc: ext of pderiv of coeff
-- statement:
--   The Formal Calc construction uses the ext of pderiv of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L122-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L122-L133

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

theorem GlobalTheory.FormalCalc.ext_of_pderiv_of_coeff [IsAddTorsionFree A] (e : ι → σ) {f g : MvPowerSeries σ A}
    (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = coeff α g) : f = g := by sorry
