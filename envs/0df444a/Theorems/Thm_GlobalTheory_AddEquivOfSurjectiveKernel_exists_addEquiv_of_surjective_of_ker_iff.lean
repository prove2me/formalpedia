-- Prove2me | Theorems.Thm_GlobalTheory_AddEquivOfSurjectiveKernel_exists_addEquiv_of_surjective_of_ker_iff
-- name    : GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:19.94954+00:00
-- url     : https://prove2.me/theorems/969f686c-57b1-4895-bd51-121dc098755e
-- title:
--   Add Equiv Of Surjective Kernel: exists add Equiv of surjective of ker iff
-- statement:
--   The Add Equiv Of Surjective Kernel construction uses the exists add Equiv of surjective of ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsAddEquivOfSurjectiveOfKerIff.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsAddEquivOfSurjectiveOfKerIff.lean#L7-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AddEquivOfSurjectiveKernel
universe u_1 u_2 u_3

theorem GlobalTheory.AddEquivOfSurjectiveKernel.exists_addEquiv_of_surjective_of_ker_iff {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by sorry
