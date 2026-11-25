-- Prove2me | Theorems.Thm_GlobalTheory_SymSupport_typeFrame_inv_val
-- name    : GlobalTheory.SymSupport.typeFrame_inv_val
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:51.4819+00:00
-- url     : https://prove2.me/theorems/026c9a14-5167-445e-9cdf-7dd9dc2474c0
-- title:
--   Sym Support: type Frame inv val
-- statement:
--   The Sym Support construction uses the type Frame inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L48-L55

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

theorem GlobalTheory.SymSupport.typeFrame_inv_val {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ ord).bas⁻¹).val =
      diagonal (Sum.elim (fun _ => 1) fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by sorry
