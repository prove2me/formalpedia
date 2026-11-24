-- Prove2me | Theorems.Thm_GlobalTheory_card_kernel_quot_of_bijective
-- name    : GlobalTheory.card_kernel_quot_of_bijective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:16.931995+00:00
-- url     : https://prove2.me/theorems/9442bd7a-db72-4b10-aeb6-20d34aaf9765
-- title:
--   Global Theory: card kernel quot of bijective
-- statement:
--   The Global Theory construction uses the card kernel quot of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardKernelQuotOfBijective.lean#L7-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardKernelQuotOfBijective.lean#L7-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardKernelQuotOfBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
open GlobalTheory

theorem GlobalTheory.card_kernel_quot_of_bijective (O : Type) [CommRing O] (P : Type) [AddCommGroup P]
    [Module O P] (N : Submodule O P) (T : P →ₗ[O] P) (hT : Function.Bijective T)
    (hN : ∀ x ∈ N, T x ∈ N) :
    Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N} =
      Nat.card (↥N ⧸ (N.map T).comap N.subtype) := by sorry
