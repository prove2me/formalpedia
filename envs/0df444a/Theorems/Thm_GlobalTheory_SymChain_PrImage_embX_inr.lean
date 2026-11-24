-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_PrImage_embX_inr
-- name    : GlobalTheory.SymChain.PrImage.embX_inr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:47.80386+00:00
-- url     : https://prove2.me/theorems/6dd603c3-a71f-4214-b954-f410bde7af88
-- title:
--   Pr Image: emb X inr
-- statement:
--   The Pr Image construction uses the emb X inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean#L53-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean#L53-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.PrImage
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.SymChain.PrImage.embX_inr (g : GL n k) (r : n ⊕ Fin c) (i : Fin c) :
    (embX c g).val r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) := by sorry
