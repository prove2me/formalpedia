-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_toSpanSingleton_constGen_surjective
-- name    : GlobalTheory.PDivGroup.toSpanSingleton_constGen_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:38:57.316409+00:00
-- url     : https://prove2.me/theorems/9ead2a83-ee1b-4cfd-b962-e7d624cd135b
-- title:
--   PDiv Group: to Span Singleton const Gen surjective
-- statement:
--   The PDiv Group construction uses the to Span Singleton const Gen surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToSpanSingletonConstGenSurjective.lean#L46-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ToSpanSingletonConstGenSurjective.lean#L46-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ToSpanSingletonConstGenSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]
variable [Nontrivial O]

theorem GlobalTheory.PDivGroup.toSpanSingleton_constGen_surjective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := by sorry
