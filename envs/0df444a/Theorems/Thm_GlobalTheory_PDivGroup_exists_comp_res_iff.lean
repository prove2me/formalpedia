-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_exists_comp_res_iff
-- name    : GlobalTheory.PDivGroup.exists_comp_res_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:15.672834+00:00
-- url     : https://prove2.me/theorems/2ffe513e-74e6-4295-8dd5-a30299a48528
-- title:
--   PDiv Group: exists comp res iff
-- statement:
--   The PDiv Group construction uses the exists comp res iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L59-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ToSpanSingletonConstGenInjective.lean#L59-L70

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
variable (G : PDivGroup p O)

theorem GlobalTheory.PDivGroup.exists_comp_res_iff (n : ℕ) {B : Type*} [CommRing B] [Algebra O B]
    (x : G.A (n + 1) →ₐ[O] B) :
    (∃ y : G.A n →ₐ[O] B, y.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) = x) ↔
      toConv x ^ p ^ n = 1 := by sorry
