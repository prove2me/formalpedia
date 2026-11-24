-- Prove2me | Theorems.Thm_GlobalTheory_isFreeRingAction_arrow
-- name    : GlobalTheory.isFreeRingAction_arrow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:52.806455+00:00
-- url     : https://prove2.me/theorems/62767f83-1b4e-4394-83bd-6462bdf811fe
-- title:
--   Global Theory: is Free Ring Action arrow
-- statement:
--   The Global Theory construction uses the is Free Ring Action arrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L745-L762
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L745-L762

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory

theorem GlobalTheory.isFreeRingAction_arrow (G R : Type*) [Group G] [Finite G] [CommRing R]
    [MulSemiringAction G (G → R)] (hact : ∀ (g : G) (f : G → R) (x : G), (g • f) x = f (g⁻¹ * x)) :
    IsFreeRingAction G (G → R) := by sorry
