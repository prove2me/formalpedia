-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_faithful
-- name    : GlobalTheory.SemilinearModule.invariantsFunctor_faithful
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:52:45.3898+00:00
-- url     : https://prove2.me/theorems/98569e9e-8afb-4b2e-944e-918f934c8a00
-- title:
--   Semilinear Module: invariants Functor faithful
-- statement:
--   The Semilinear Module construction uses the invariants Functor faithful property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L719-L723
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L719-L723

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

theorem GlobalTheory.SemilinearModule.invariantsFunctor_faithful [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{w} G A).Faithful := by sorry
