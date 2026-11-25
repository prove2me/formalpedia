-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_hodgeTate_val
-- name    : GlobalTheory.PDivGroup.hodgeTate_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:21.75906+00:00
-- url     : https://prove2.me/theorems/d3c319ad-2cb9-49fc-b479-2bc9f6476999
-- title:
--   PDiv Group: hodge Tate val
-- statement:
--   The PDiv Group construction uses the hodge Tate val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1044-L1046
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1044-L1046

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
variable {G H : PDivGroup p O}
variable [Fact p.Prime]

theorem GlobalTheory.PDivGroup.hodgeTate_val (t : G.Tate) (n : ℕ) :
    (hodgeTate G t).1 n = dUnit O (toConv (t.pt n).toLinearMap : CartierDual O (G.A n)) := by sorry
