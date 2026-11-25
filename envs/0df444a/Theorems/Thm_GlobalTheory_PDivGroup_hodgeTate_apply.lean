-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_hodgeTate_apply
-- name    : GlobalTheory.PDivGroup.hodgeTate_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:21.510668+00:00
-- url     : https://prove2.me/theorems/9249125a-2b84-4b59-aa5e-f65e9a02b61d
-- title:
--   PDiv Group: hodge Tate apply
-- statement:
--   The PDiv Group construction uses the hodge Tate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1038-L1039
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1038-L1039

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

theorem GlobalTheory.PDivGroup.hodgeTate_apply (t : G.Tate) :
    hodgeTate G t = dlog G.dual (tateMap G G.dual.dual O G.bidual.hom t) := by sorry
