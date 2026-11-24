-- Prove2me | Theorems.Thm_GlobalTheory_groupAlgebra_single_one_mem_of_span
-- name    : GlobalTheory.groupAlgebra_single_one_mem_of_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:28.539639+00:00
-- url     : https://prove2.me/theorems/24c1ce1d-cd7c-4b51-9c4c-fe020de0dae8
-- title:
--   Global Theory: group Algebra single one mem of span
-- statement:
--   The Global Theory construction uses the group Algebra single one mem of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupAlgebraSingleOneMemOfSpan.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupAlgebraSingleOneMemOfSpan.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.groupAlgebra_single_one_mem_of_span {A X : Type} [CommRing A] [AddCommGroup X]
    (R : Subring (AddMonoidAlgebra A X)) (h0 : ∀ a : A, AddMonoidAlgebra.single 0 a ∈ R) (α : X)
    (h : Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R} = ⊤) :
    AddMonoidAlgebra.single α (1 : A) ∈ R := by sorry
