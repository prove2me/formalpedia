-- Prove2me | Theorems.Thm_GlobalTheory_unitBall_eq_of_integral_dvr
-- name    : GlobalTheory.unitBall_eq_of_integral_dvr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:32.101497+00:00
-- url     : https://prove2.me/theorems/f3f6aeb9-b68e-46e9-b4a4-751ac48e9eae
-- title:
--   Global Theory: unit Ball eq of integral dvr
-- statement:
--   The Global Theory construction uses the unit Ball eq of integral dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallEqOfIntegralDvr.lean#L5-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallEqOfIntegralDvr.lean#L5-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallEqOfIntegralDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.unitBall_eq_of_integral_dvr (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [IsLocalHom (algebraMap V W)]
    (hinj : Function.Injective (algebraMap V W))
    (κ : FractionRing V →+* PadicAlgCl p) (κ' : FractionRing W →+* PadicAlgCl p)
    (hc : ∀ v : V, κ' (algebraMap W (FractionRing W) (algebraMap V W v)) =
      κ (algebraMap V (FractionRing V) v))
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by sorry
