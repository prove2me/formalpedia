-- Prove2me | Theorems.Thm_GlobalTheory_det_sub_det_mem_span_of_mulVec_eq
-- name    : GlobalTheory.det_sub_det_mem_span_of_mulVec_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:36.408022+00:00
-- url     : https://prove2.me/theorems/e5a7e16f-c49c-4327-9845-9e85ea0df8f5
-- title:
--   Global Theory: det sub det mem span of mul Vec eq
-- statement:
--   The Global Theory construction uses the det sub det mem span of mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetUpdateRowAlternatingMulVecMem.lean#L69-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetUpdateRowAlternatingMulVecMem.lean#L69-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetUpdateRowAlternatingMulVecMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.det_sub_det_mem_span_of_mulVec_eq :
    ∀ (T : Type) [CommRing T] (g : ℕ) (x : Fin g → T), (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) → ∀ c c' : Matrix (Fin g) (Fin g) T, c.mulVec x = c'.mulVec x → c.det - c'.det ∈ Ideal.span (Set.range (c.mulVec x)) := by sorry
