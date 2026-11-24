-- Prove2me | Theorems.Thm_GlobalTheory_FlatFactor_UpStage_embA_tv_mem
-- name    : GlobalTheory.FlatFactor.UpStage.embA_tv_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:05:45.4378+00:00
-- url     : https://prove2.me/theorems/b800e812-2232-4887-a577-3c80e8d4425b
-- title:
--   Up Stage: emb A tv mem
-- statement:
--   The Up Stage construction uses the emb A tv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelIntegratesFreeEntries.lean#L247-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelIntegratesFreeEntries.lean#L247-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelIntegratesFreeEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.UpStage
variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ)
variable {n n' c ρ}
variable {k : Type} [Field k]

theorem GlobalTheory.FlatFactor.UpStage.embA_tv_mem (i j : Fin c) (h : i ≠ j) (hij : i.val < j.val) (a : k) (p : ℕ) :
    embA n (tv i j h a) ∈ N k n c p := by sorry
