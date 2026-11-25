-- Prove2me | Theorems.Thm_GlobalTheory_T_fockDetCharInvariants_le_span_prodMaximalMinors
-- name    : GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:43:15.908196+00:00
-- url     : https://prove2.me/theorems/749388f6-0f7b-459a-9561-b517e330c613
-- title:
--   T: fock Det Char Invariants le span prod Maximal Minors
-- statement:
--   The T construction uses the fock Det Char Invariants le span prod Maximal Minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinorsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinorsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by sorry
