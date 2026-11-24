-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_integral_psi_box
-- name    : GlobalTheory.LocFlat.UnramFlat.integral_psi_box
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:28:24.893837+00:00
-- url     : https://prove2.me/theorems/4c6e7c74-d8ef-42e4-bb44-6c073fe3a45e
-- title:
--   Unram Flat: integral psi box
-- statement:
--   The Unram Flat construction uses the integral psi box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L202-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L202-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEmbXMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatContrIntIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option linter.unusedSectionVars false
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.UnramFlat
open GlobalTheory.RootEx.Unram GlobalTheory.LocFlat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n]
open Classical

theorem GlobalTheory.LocFlat.UnramFlat.integral_psi_box {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (u : n → k) :
    ∫ y, (if ∀ r, y r ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (u ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ : n => ν) =
      if ∀ r, u r ∈ 𝒪[k] then 1 else 0 := by sorry
