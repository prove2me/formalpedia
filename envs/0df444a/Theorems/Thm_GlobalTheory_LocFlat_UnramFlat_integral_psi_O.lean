-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_UnramFlat_integral_psi_O
-- name    : GlobalTheory.LocFlat.UnramFlat.integral_psi_O
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:39.321638+00:00
-- url     : https://prove2.me/theorems/dedd58dc-d0be-435d-b976-2574e49c696c
-- title:
--   Unram Flat: integral psi O
-- statement:
--   The Unram Flat construction uses the integral psi O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L159-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatContrIntIndicator.lean#L159-L196

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
open Classical

theorem GlobalTheory.LocFlat.UnramFlat.integral_psi_O {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) (a : k) :
    ∫ t, (if t ∈ 𝒪[k] then (1 : ℂ) else 0) * (ψ (-1 * (a * t)) : ℂ) ∂ν = if a ∈ 𝒪[k] then 1 else 0 := by sorry
