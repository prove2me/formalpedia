-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_fourier_eq_zero
-- name    : GlobalTheory.SplitWeil.fourier_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:58.433258+00:00
-- url     : https://prove2.me/theorems/c5a52818-230a-409c-90af-ca646fa1803f
-- title:
--   Split Weil: fourier eq zero
-- statement:
--   The Split Weil construction uses the fourier eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L348-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L348-L359

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

theorem GlobalTheory.SplitWeil.fourier_eq_zero (h : HasConductor ψ c) {s : kˣ} {f : k → ℂ}
    (hs : ∀ t ∈ cball s, ∀ x, f (x + t) = f x) {y : k} (hy : y ∉ cball (c * s⁻¹)) :
    ∫ x, f x * (ψ (x * y) : ℂ) ∂ν = 0 := by sorry
