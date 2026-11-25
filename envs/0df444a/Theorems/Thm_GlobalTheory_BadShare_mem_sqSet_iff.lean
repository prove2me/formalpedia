-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_mem_sqSet_iff
-- name    : GlobalTheory.BadShare.mem_sqSet_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:23.417729+00:00
-- url     : https://prove2.me/theorems/a21a0dca-7fbc-4d3e-8d3d-ff9e790da385
-- title:
--   Bad Share: mem sq Set iff
-- statement:
--   The Bad Share construction uses the mem sq Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemMonicSquarefreeUnitConstPolysIffMonicSquarefr.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemMonicSquarefreeUnitConstPolysIffMonicSquarefr.lean#L8-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
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

theorem GlobalTheory.BadShare.mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by sorry
