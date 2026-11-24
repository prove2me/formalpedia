-- Prove2me | Theorems.Thm_GlobalTheory_topologicalClosure_stable_of_continuousLinearMap
-- name    : GlobalTheory.topologicalClosure_stable_of_continuousLinearMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:47.315511+00:00
-- url     : https://prove2.me/theorems/55df617f-0c88-4b4e-9a06-beac0c5b549d
-- title:
--   Global Theory: topological Closure stable of continuous Linear Map
-- statement:
--   The Global Theory construction uses the topological Closure stable of continuous Linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzClosureStableLinearFormFourier.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzClosureStableLinearFormFourier.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzClosureStableLinearFormFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by sorry
