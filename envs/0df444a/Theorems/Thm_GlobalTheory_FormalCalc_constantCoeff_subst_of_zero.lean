-- Prove2me | Theorems.Thm_GlobalTheory_FormalCalc_constantCoeff_subst_of_zero
-- name    : GlobalTheory.FormalCalc.constantCoeff_subst_of_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:33:55.329515+00:00
-- url     : https://prove2.me/theorems/188c4daa-2622-46d1-817d-bbae00ad57e1
-- title:
--   Formal Calc: constant Coeff subst of zero
-- statement:
--   The Formal Calc construction uses the constant Coeff subst of zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L95-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NatCastMulCoeffOfPderivEq.lean#L95-L102

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
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GlobalTheory.FormalCalc.constantCoeff_subst_of_zero {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by sorry
