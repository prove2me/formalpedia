-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_toSpanSingleton_constGen_injective
-- name    : GlobalTheory.PDivGroup.toSpanSingleton_constGen_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:55.50273+00:00
-- url     : https://prove2.me/theorems/85456909-8abe-4e48-be85-ad9f096c79c4
-- title:
--   PDiv Group: to Span Singleton const Gen injective
-- statement:
--   The PDiv Group construction uses the to Span Singleton const Gen injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1246-L1255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1246-L1255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory
open PDiv
open GlobalTheory.PDivGroup
attribute [instance] commRing hopf cocomm finite projective
variable {p : ℕ} {O : Type} [CommRing O]
variable (p O) [Fact p.Prime]

theorem GlobalTheory.PDivGroup.toSpanSingleton_constGen_injective [Nontrivial O] :
    Function.Injective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := by sorry
