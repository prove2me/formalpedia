-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pullTwo_id
-- name    : GlobalTheory.PDiv.pullTwo_id
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:40.33289+00:00
-- url     : https://prove2.me/theorems/ede7ab47-fffa-4fa3-b018-1e68b2a58065
-- title:
--   PDiv: pull Two id
-- statement:
--   The PDiv construction uses the pull Two id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/EqZeroOfCobOneEqZero.lean#L91-L95

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

theorem GlobalTheory.PDiv.pullTwo_id (c : A ⊗[O] A) : pullbackTwo (BialgHom.id O A) c = c := by sorry
