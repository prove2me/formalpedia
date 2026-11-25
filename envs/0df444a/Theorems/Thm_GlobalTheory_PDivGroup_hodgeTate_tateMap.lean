-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_hodgeTate_tateMap
-- name    : GlobalTheory.PDivGroup.hodgeTate_tateMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:29:11.893833+00:00
-- url     : https://prove2.me/theorems/e1e13cc5-d778-4479-ba25-ee4a933e59ac
-- title:
--   PDiv Group: hodge Tate tate Map
-- statement:
--   The PDiv Group construction uses the hodge Tate tate Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1052-L1055
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L1052-L1055

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

theorem GlobalTheory.PDivGroup.hodgeTate_tateMap (f : G ⟶ H) (t : G.Tate) :
    hodgeTate H (tateMap G H O f t) = omegaDualMap G H f (hodgeTate G t) := by sorry
