-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_full
-- name    : GlobalTheory.SemilinearModule.invariantsFunctor_full
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:05.763691+00:00
-- url     : https://prove2.me/theorems/1f6afd25-501c-4d47-a22c-0edef99da0fc
-- title:
--   Semilinear Module: invariants Functor full
-- statement:
--   The Semilinear Module construction uses the invariants Functor full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L725-L730
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L725-L730

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
open GlobalTheory.SemilinearModule
attribute [instance] addCommGroup module action semilinear
variable (G : Type v) [Group G] (A : Type u) [CommRing A] [MulSemiringAction G A]
variable {G A}

theorem GlobalTheory.SemilinearModule.invariantsFunctor_full [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{w} G A).Full := by sorry
