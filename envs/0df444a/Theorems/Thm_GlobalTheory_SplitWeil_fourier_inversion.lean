-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_fourier_inversion
-- name    : GlobalTheory.SplitWeil.fourier_inversion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:48.96811+00:00
-- url     : https://prove2.me/theorems/e06de18d-6c0c-408c-8a68-d49d02b9b6e4
-- title:
--   Split Weil: fourier inversion
-- statement:
--   The Split Weil construction uses the fourier inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L388-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L388-L429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {ψ : AddChar k Circle} {c : kˣ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem GlobalTheory.SplitWeil.fourier_inversion (h : HasConductor ψ c) {f : k → ℂ} (hf : f ∈ SB k) :
    ∫ y, (∫ x, f x * (ψ (x * y) : ℂ) ∂ν) ∂ν =
      ((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c : ℝ) : ℂ) * f 0 := by sorry
