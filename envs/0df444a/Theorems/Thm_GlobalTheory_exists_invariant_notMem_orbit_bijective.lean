-- Prove2me | Theorems.Thm_GlobalTheory_exists_invariant_notMem_orbit_bijective
-- name    : GlobalTheory.exists_invariant_notMem_orbit_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:16.037294+00:00
-- url     : https://prove2.me/theorems/3573bde8-b4c7-5822-ad99-063d2a8561a0
-- title:
--   Global Theory: exists invariant not Mem orbit bijective
-- statement:
--   The Global Theory construction uses the exists invariant not Mem orbit bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L888-L897
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L888-L897

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory

theorem GlobalTheory.exists_invariant_notMem_orbit_bijective (G : Type*) [Group G] [Finite G] {A : Type*}
    [CommRing A] [MulSemiringAction G A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (Q : Ideal A) [Q.IsPrime] :
    ∃ (s : A) (e : M), (∀ g : G, g • s = s) ∧ (∀ g : G, s ∉ g • Q) ∧
      Function.Bijective (LinearMap.toSpanSingleton (Localization.Away s)
        (LocalizedModule (.powers s) M) (LocalizedModule.mkLinearMap (.powers s) M e)) := by sorry
