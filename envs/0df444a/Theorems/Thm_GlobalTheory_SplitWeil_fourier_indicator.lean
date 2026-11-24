-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_fourier_indicator
-- name    : GlobalTheory.SplitWeil.fourier_indicator
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:21:49.793536+00:00
-- url     : https://prove2.me/theorems/6f1c8819-041c-4c4a-ac8c-ca8b106672f8
-- title:
--   Split Weil: fourier indicator
-- statement:
--   The Split Weil construction uses the fourier indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L361-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L361-L386

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

theorem GlobalTheory.SplitWeil.fourier_indicator (h : HasConductor ψ c) (s : kˣ) (x : k) :
    ∫ y, (cball (c * s⁻¹)).indicator (fun _ => (1 : ℂ)) y * (ψ (y * x) : ℂ) ∂ν =
      (cball s).indicator (fun _ => (ν.real (cball (c * s⁻¹)) : ℂ)) x := by sorry
