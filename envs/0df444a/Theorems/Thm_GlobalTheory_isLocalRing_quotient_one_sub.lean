-- Prove2me | Theorems.Thm_GlobalTheory_isLocalRing_quotient_one_sub
-- name    : GlobalTheory.isLocalRing_quotient_one_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:04.629424+00:00
-- url     : https://prove2.me/theorems/138e7105-e70e-4bcb-ba14-69be7da76d6f
-- title:
--   Global Theory: is Local Ring quotient one sub
-- statement:
--   The Global Theory construction uses the is Local Ring quotient one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L329-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L329-L342

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.isLocalRing_quotient_one_sub {S : Type*} [CommRing S] {e : S} (he : IsIdempotentElem e)
    (q : Ideal S) [hq : q.IsMaximal] (H : ∀ n : Ideal S, n.IsMaximal → (e ∉ n ↔ n = q)) :
    IsLocalRing (S ⧸ Ideal.span {1 - e}) := by sorry
