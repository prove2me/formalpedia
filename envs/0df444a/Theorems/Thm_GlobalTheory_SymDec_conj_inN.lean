-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_conj_inN
-- name    : GlobalTheory.SymDec.conj_inN
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:17:28.474631+00:00
-- url     : https://prove2.me/theorems/705881b5-649c-527c-b645-874c0f723834
-- title:
--   Sym Dec: conj in N
-- statement:
--   The Sym Dec construction uses the conj in N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L84-L91

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
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymDec.conj_inN (ϖ : kˣ) (hc : 0 + c = c) (p : ℕ) {g : GL (Fin κ ⊕ Fin c) k} (hg : InN p g) :
    InN p ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)) := by sorry
