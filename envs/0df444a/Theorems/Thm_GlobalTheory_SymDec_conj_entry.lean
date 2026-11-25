-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_conj_entry
-- name    : GlobalTheory.SymDec.conj_entry
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:21.537287+00:00
-- url     : https://prove2.me/theorems/074996f8-011a-5154-82b0-edf61c48b9e5
-- title:
--   Sym Dec: conj entry
-- statement:
--   The Sym Dec construction uses the conj entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L46-L50

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

theorem GlobalTheory.SymDec.conj_entry [Fintype ι] [DecidableEq ι] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL ι k) (r s : n ⊕ Fin c) :
    ((typeFrame ϖ ord).conj g).val r s = dg ϖ r * g.val (ord.symm r) (ord.symm s) * (dg ϖ s)⁻¹ := by sorry
