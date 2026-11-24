-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_continuousAt_of_pointwise_of_bounded
-- name    : GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:07.859097+00:00
-- url     : https://prove2.me/theorems/31bccdff-f559-4649-ab0b-6e502a45b604
-- title:
--   Global Theory: schwartz continuous At of pointwise of bounded
-- statement:
--   The Global Theory construction uses the schwartz continuous At of pointwise of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L157-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzContinuousAtOfPointwiseOfBounded.lean#L157-L197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.schwartz_continuousAt_of_pointwise_of_bounded :
    ∀ {X : Type} [TopologicalSpace X] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : X → SchwartzMap V ℂ) (x0 : X), (∀ v, ContinuousAt (fun x => F x v) x0) →
    (∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in nhds x0, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (F x) v‖ ≤ C) → ContinuousAt F x0 := by sorry
