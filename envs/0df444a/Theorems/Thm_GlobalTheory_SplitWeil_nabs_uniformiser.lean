-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_nabs_uniformiser
-- name    : GlobalTheory.SplitWeil.nabs_uniformiser
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:43.103802+00:00
-- url     : https://prove2.me/theorems/2ef6afd4-ea5e-4851-8588-a9506cc12015
-- title:
--   Split Weil: nabs uniformiser
-- statement:
--   The Split Weil construction uses the nabs uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L148-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L148-L185

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

theorem GlobalTheory.SplitWeil.nabs_uniformiser {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {x : kˣ} (hx : (x : k) = ϖ) :
    nabs k x = (resCard k : ℝ)⁻¹ := by sorry
