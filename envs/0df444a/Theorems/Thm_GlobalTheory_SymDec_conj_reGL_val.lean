-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_conj_reGL_val
-- name    : GlobalTheory.SymDec.conj_reGL_val
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:16:02.663164+00:00
-- url     : https://prove2.me/theorems/63041a58-d607-5a94-83f0-fe96535e53d9
-- title:
--   Sym Dec: conj re GL val
-- statement:
--   The Sym Dec construction uses the conj re GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L79-L82

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

theorem GlobalTheory.SymDec.conj_reGL_val (ϖ : kˣ) (hc : 0 + c = c) (g : GL (Fin κ ⊕ Fin c) k) (r s : XIx (Fin κ) t 0 ⊕ Fin c) :
    ((typeFrame ϖ (stdOrd (Fin κ) t 0 c hc)).conj (reGL (ixZero (Fin κ ⊕ Fin c) t) g)).val r s =
      dg ϖ r * g.val ((ordZ t hc).symm r) ((ordZ t hc).symm s) * (dg ϖ s)⁻¹ := by sorry
