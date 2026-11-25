-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_mulBy_of_cobOne_eq_zero
-- name    : GlobalTheory.PDiv.mulBy_of_cobOne_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:38.690415+00:00
-- url     : https://prove2.me/theorems/2589c435-f691-4da5-92aa-3710f8986940
-- title:
--   PDiv: mul By of cob One eq zero
-- statement:
--   The PDiv construction uses the mul By of cob One eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L97-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L97-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__EqZeroOfCobOneEqZero_fe26957659067348
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDiv
variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

theorem GlobalTheory.PDiv.mulBy_of_cobOne_eq_zero [IsCocomm O A] {b : A} (hb : cobOne O A b = 0) (k : ℕ) :
    mulBy O A k b = k • b ∧ counit (R := O) b = 0 := by sorry
