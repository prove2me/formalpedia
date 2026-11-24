-- Prove2me | Theorems.Thm_GlobalTheory_SCV_eq_of_invariant_realSubspace
-- name    : GlobalTheory.SCV.eq_of_invariant_realSubspace
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:31:43.048564+00:00
-- url     : https://prove2.me/theorems/bccd6d7c-c93a-4b50-87bb-7b06d371894b
-- title:
--   SCV: eq of invariant real Subspace
-- statement:
--   The SCV construction uses the eq of invariant real Subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L61-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem GlobalTheory.SCV.eq_of_invariant_realSubspace {f : E → V} {U : Set E} {S : Submodule ℝ E}
    (hS : Submodule.span ℂ (S : Set E) = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (h : ∀ z ∈ U, ∀ s ∈ S, z + s ∈ U → f (z + s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by sorry
