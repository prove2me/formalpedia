-- Prove2me | Theorems.Thm_GlobalTheory_T_existsUnique_place_ord_eq_one_of_transcendental_generator
-- name    : GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:24.811246+00:00
-- url     : https://prove2.me/theorems/892466bf-853a-5db7-a3fb-ee7a6cd649b9
-- title:
--   T: exists Unique place ord eq one of transcendental generator
-- statement:
--   The T construction uses the exists Unique place ord eq one of transcendental generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniquePlaceOrdEqOneStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUniquePlaceOrdEqOneStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniquePlaceOrdEqOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by sorry
