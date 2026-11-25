-- Prove2me | Theorems.Thm_GlobalTheory_FlatFactor_LowStage_kerRed_evAll
-- name    : GlobalTheory.FlatFactor.LowStage.kerRed_evAll
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:58.466292+00:00
-- url     : https://prove2.me/theorems/2a8ec0bf-d7f6-4140-9f1a-52c702475d57
-- title:
--   Low Stage: ker Red ev All
-- statement:
--   The Low Stage construction uses the ker Red ev All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelAllNonFreeUnreadEntries.lean#L351-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFactorReductionKernelAllNonFreeUnreadEntries.lean#L351-L412

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelReductionExtendEvaluatedIntegrated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LinearMapKillingPartialEvalIntegralKernelTransla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFactorReductionKernelAllNonFreeUnreadEntries
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
open GlobalTheory GlobalTheory.FlatFactor GlobalTheory.FlatFactor.LowStage
open MeasureTheory ValuativeRel Matrix

theorem GlobalTheory.FlatFactor.LowStage.kerRed_evAll : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (l : _root_.GlobalTheory.SplitWeil.SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → _root_.GlobalTheory.FlatFactor.TwLaw ρ ψ l → _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evC n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l → _root_.GlobalTheory.FlatFactor.KerRed ν (_root_.GlobalTheory.FlatFactor.evAll n n' c ρ) (_root_.GlobalTheory.FlatFactor.itB n n' c ρ) (_root_.GlobalTheory.RootEx.basePt c (0 : Matrix n n' k)) l := by sorry
