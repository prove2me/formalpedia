-- Prove2me | Theorems.Thm_GlobalTheory_PartRed_kills_evals
-- name    : GlobalTheory.PartRed.kills_evals
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:15.25481+00:00
-- url     : https://prove2.me/theorems/9b3c4880-3dc4-4df3-95b9-2ad3669f7b5b
-- title:
--   Part Red: kills evals
-- statement:
--   The Part Red construction uses the kills evals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapLawsFactorFourierJacobiSource.lean#L119-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapLawsFactorFourierJacobiSource.lean#L119-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionIntegrateEntryOfTranslationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionUpperFreeEntryTranslationLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqFlatMapFourierJacobiRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAddStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapLawsFactorFourierJacobiSource
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] {M : Type} [AddCommGroup M]
  [Module ℂ M]

theorem GlobalTheory.PartRed.kills_evals (ψ : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hν : ν.IsAddHaarMeasure) (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k)
    (I : Finset (R × Q)) (S : Finset (R × Q)) : ∀ E : Finset (R × Q), Disjoint S I → Kills L ψ ν w β E I →
    (∀ e ∈ S, ∀ E' : Finset (R × Q), E ⊆ E' → E' ⊆ E ∪ S → e ∉ E' → EvalLaw L ψ ν w β E' I e) →
    Kills L ψ ν w β (E ∪ S) I := by sorry
