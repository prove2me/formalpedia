-- Prove2me | Theorems.Thm_GlobalTheory_SymSupport_InR_conj
-- name    : GlobalTheory.SymSupport.InR.conj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:32.382596+00:00
-- url     : https://prove2.me/theorems/ef96a3c4-79ce-5b3c-9816-86eb8e4960ea
-- title:
--   In R: conj
-- statement:
--   The In R construction uses the conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L57-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L57-L64

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

theorem GlobalTheory.SymSupport.InR.conj {ι : Type*} (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) {g : GL (n ⊕ Fin c) k} (h : InR g.val) :
    InR ((typeFrame ϖ ord).bas * g * (typeFrame ϖ ord).bas⁻¹).val := by sorry
