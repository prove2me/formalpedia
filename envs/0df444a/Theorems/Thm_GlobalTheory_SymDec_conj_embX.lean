-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_conj_embX
-- name    : GlobalTheory.SymDec.conj_embX
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:37.061188+00:00
-- url     : https://prove2.me/theorems/a142bf46-ab53-4bac-b4e1-5ca258dc2177
-- title:
--   Sym Dec: conj emb X
-- statement:
--   The Sym Dec construction uses the conj emb X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L93-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L93-L117

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

theorem GlobalTheory.SymDec.conj_embX (ϖ : kˣ) (hc : 0 + c = c) (γ : GL (Fin κ) k) :
    (typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) (embX c γ)) =
      embX c (reGL (epsZ t) γ) := by sorry
