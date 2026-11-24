-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_PrImage_conj_symm_apply
-- name    : GlobalTheory.SymChain.PrImage.conj_symm_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:53.099795+00:00
-- url     : https://prove2.me/theorems/fbc37c3e-b37c-4bb2-a3f5-31975836b02c
-- title:
--   Pr Image: conj symm apply
-- statement:
--   The Pr Image construction uses the conj symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean#L58-L60

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

theorem GlobalTheory.SymChain.PrImage.conj_symm_apply (F : LatFrame k ι (n ⊕ Fin c)) (y : GL (n ⊕ Fin c) k) :
    F.conj.symm y = (reGL F.ord).symm (F.bas⁻¹ * y * F.bas) := by sorry
