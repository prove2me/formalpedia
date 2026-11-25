-- Prove2me | Theorems.Thm_GlobalTheory_T_rootExchangeRowUnipotent_latticeFrame_conj_apply
-- name    : GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:16:49.051841+00:00
-- url     : https://prove2.me/theorems/2c2bb6f2-e1d9-48b5-8df4-f14e3c2085c6
-- title:
--   T: root Exchange Row Unipotent lattice Frame conj apply
-- statement:
--   The T construction uses the root Exchange Row Unipotent lattice Frame conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeRowUnipotentLatticeFrameConjApplyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeRowUnipotentLatticeFrameConjApplyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApplyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by sorry
