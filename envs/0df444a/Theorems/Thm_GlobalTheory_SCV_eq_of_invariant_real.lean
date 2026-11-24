-- Prove2me | Theorems.Thm_GlobalTheory_SCV_eq_of_invariant_real
-- name    : GlobalTheory.SCV.eq_of_invariant_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:17.021658+00:00
-- url     : https://prove2.me/theorems/70811fbb-809b-4ead-87c7-ec7b4eea41ba
-- title:
--   SCV: eq of invariant real
-- statement:
--   The SCV construction uses the eq of invariant real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EventuallyIteratedFDerivEqZeroOfRealSubspace.lean#L105-L111

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
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.SCV.eq_of_invariant_real {f : (ι → ℂ) → V} {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ x : ι → ℝ, (z + fun i => (x i : ℂ)) ∈ U → f (z + fun i => (x i : ℂ)) = f z)
    {z w : ι → ℂ} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by sorry
