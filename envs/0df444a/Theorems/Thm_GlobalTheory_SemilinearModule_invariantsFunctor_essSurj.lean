-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_essSurj
-- name    : GlobalTheory.SemilinearModule.invariantsFunctor_essSurj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:22.483391+00:00
-- url     : https://prove2.me/theorems/66959ee0-be9e-4d1f-b806-4fe91826beaa
-- title:
--   Semilinear Module: invariants Functor ess Surj
-- statement:
--   The Semilinear Module construction uses the invariants Functor ess Surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L732-L735
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L732-L735

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

theorem GlobalTheory.SemilinearModule.invariantsFunctor_essSurj [Finite G] (h : IsFreeRingAction G A) :
    (invariantsFunctor.{max w u} G A).EssSurj := by sorry
