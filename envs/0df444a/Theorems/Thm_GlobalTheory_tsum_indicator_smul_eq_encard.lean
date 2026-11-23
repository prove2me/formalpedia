-- Prove2me | Theorems.Thm_GlobalTheory_tsum_indicator_smul_eq_encard
-- name    : GlobalTheory.tsum_indicator_smul_eq_encard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:10.085664+00:00
-- url     : https://prove2.me/theorems/4cfea7c0-7bb1-46a2-a0b3-b5c045b6a4f3
-- title:
--   Global Theory: tsum indicator smul eq encard
-- statement:
--   The Global Theory construction uses the tsum indicator smul eq encard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}
omit [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G]

theorem GlobalTheory.tsum_indicator_smul_eq_encard (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by sorry
