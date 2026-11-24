-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_integral_mul_mem_SB
-- name    : GlobalTheory.RootEx.integral_mul_mem_SB
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:18.022284+00:00
-- url     : https://prove2.me/theorems/9111cd7c-c175-4489-80ef-9a0e8ca92a95
-- title:
--   Root Ex: integral mul mem SB
-- statement:
--   The Root Ex construction uses the integral mul mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsClosedEmbeddingAffPtUncurry.lean#L11-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx

theorem GlobalTheory.RootEx.integral_mul_mem_SB {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [R1Space X]
    [MeasurableSpace E] (μ : Measure E) (G : X × E → ℂ) (hG : G ∈ SB (X × E)) (χ : E → ℂ) :
    (fun x => ∫ e, G (x, e) * χ e ∂μ) ∈ SB X := by sorry
