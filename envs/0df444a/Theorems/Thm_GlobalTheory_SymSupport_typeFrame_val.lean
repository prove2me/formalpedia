-- Prove2me | Theorems.Thm_GlobalTheory_SymSupport_typeFrame_val
-- name    : GlobalTheory.SymSupport.typeFrame_val
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:05.949957+00:00
-- url     : https://prove2.me/theorems/e2cfa5ac-74c0-5088-879d-bda252f532b5
-- title:
--   Sym Support: type Frame val
-- statement:
--   The Sym Support construction uses the type Frame val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L43-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
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
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.SymSupport.typeFrame_val {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    (typeFrame ϖ ord).bas.val = diagonal (Sum.elim (fun _ => 1) fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by sorry
