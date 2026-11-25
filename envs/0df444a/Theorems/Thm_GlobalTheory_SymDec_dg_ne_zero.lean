-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_dg_ne_zero
-- name    : GlobalTheory.SymDec.dg_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:29.658306+00:00
-- url     : https://prove2.me/theorems/b9ca5079-2141-5516-8327-d18b8816909c
-- title:
--   Sym Dec: dg ne zero
-- statement:
--   The Sym Dec construction uses the dg ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L33-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.SymDec.dg_ne_zero (ϖ : kˣ) (r : n ⊕ Fin c) : dg ϖ r ≠ 0 := by sorry
