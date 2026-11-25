-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree
-- name    : GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:52:04.268999+00:00
-- url     : https://prove2.me/theorems/10fc0b0d-4a80-5618-8814-d0b45436b0ae
-- title:
--   T: mem monic Squarefree Unit Const Polys iff monic squarefree
-- statement:
--   The T construction uses the mem monic Squarefree Unit Const Polys iff monic squarefree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (f : (ZMod g)[X]), f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by sorry
