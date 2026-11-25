-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_lev_ordZ_symm
-- name    : GlobalTheory.SymDec.lev_ordZ_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:09.441046+00:00
-- url     : https://prove2.me/theorems/f51b0313-2d83-46be-9a64-a7efaa5b6153
-- title:
--   Sym Dec: lev ord Z symm
-- statement:
--   The Sym Dec construction uses the lev ord Z symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L69-L75

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

theorem GlobalTheory.SymDec.lev_ordZ_symm (hc : 0 + c = c) (p : ℕ) (z : XIx (Fin κ) t 0 ⊕ Fin c) :
    lev p ((ordZ t hc).symm z) = lev p z := by sorry
