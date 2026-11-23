-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_natCast_mul_coeff_of_pderiv_eq
-- name    : GlobalTheory.FormalCalc.natCast_mul_coeff_of_pderiv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:54.134072+00:00
-- url     : https://prove2.me/theorems/a360ff01-98be-4b48-8a53-914f9e3db118
-- title:
--   Formal Calc: nat Cast mul coeff of pderiv eq
-- statement:
--   The Formal Calc construction uses the nat Cast mul coeff of pderiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L115-L120

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

theorem GlobalTheory.FormalCalc.natCast_mul_coeff_of_pderiv_eq {f a : MvPowerSeries σ A} {s : σ}
    (h : pderiv A s f = a) {α : σ →₀ ℕ} (hα : α s ≠ 0) :
    (α s : A) * coeff α f = coeff (α - single s 1) a := by sorry
