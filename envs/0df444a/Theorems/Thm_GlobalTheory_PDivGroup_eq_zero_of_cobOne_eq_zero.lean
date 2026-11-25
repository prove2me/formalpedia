-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_eq_zero_of_cobOne_eq_zero
-- name    : GlobalTheory.PDivGroup.eq_zero_of_cobOne_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:46.06233+00:00
-- url     : https://prove2.me/theorems/96a13227-54f3-4737-9b4a-285035c19782
-- title:
--   PDiv Group: eq zero of cob One eq zero
-- statement:
--   The PDiv Group construction uses the eq zero of cob One eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L171-L175

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
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G H K : PDivGroup p O)

theorem GlobalTheory.PDivGroup.eq_zero_of_cobOne_eq_zero [IsDomain O] (hp : (p : O) ≠ 0) (n : ℕ) {b : G.A n}
    (hb : cobOne O _ b = 0) : b = 0 := by sorry
