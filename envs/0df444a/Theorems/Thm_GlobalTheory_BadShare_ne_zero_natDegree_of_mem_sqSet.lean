-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_ne_zero_natDegree_of_mem_sqSet
-- name    : GlobalTheory.BadShare.ne_zero_natDegree_of_mem_sqSet
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:03.260627+00:00
-- url     : https://prove2.me/theorems/6389b2d9-9077-495f-88fe-6e55ed713f06
-- title:
--   Bad Share: ne zero nat Degree of mem sq Set
-- statement:
--   The Bad Share construction uses the ne zero nat Degree of mem sq Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusCardBoundsAndMul.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusCardBoundsAndMul.lean#L27-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusCardBoundsAndMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare

theorem GlobalTheory.BadShare.ne_zero_natDegree_of_mem_sqSet (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X])
    (hf : f ∈ sqSet g N) : f ≠ 0 ∧ f.natDegree = N := by sorry
