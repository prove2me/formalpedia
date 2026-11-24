-- Prove2me | Theorems.Thm_GlobalTheory_card_eq_finrank_of_points
-- name    : GlobalTheory.card_eq_finrank_of_points
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:51.486077+00:00
-- url     : https://prove2.me/theorems/9473fb89-b16a-43cd-9c0b-52f7575767b9
-- title:
--   Global Theory: card eq finrank of points
-- statement:
--   The Global Theory construction uses the card eq finrank of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L88-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]

theorem GlobalTheory.card_eq_finrank_of_points (P : ι ≃ (S →ₐ[R] E)) : Fintype.card ι = finrank R S := by sorry
