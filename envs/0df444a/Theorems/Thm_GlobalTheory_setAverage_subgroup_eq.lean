-- Prove2me | Theorems.Thm_GlobalTheory_setAverage_subgroup_eq
-- name    : GlobalTheory.setAverage_subgroup_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:12.538189+00:00
-- url     : https://prove2.me/theorems/fcd08764-16d7-4312-8997-566ee62e9da3
-- title:
--   Global Theory: set Average subgroup eq
-- statement:
--   The Global Theory construction uses the set Average subgroup eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L295-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L295-L302

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
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E]

theorem GlobalTheory.setAverage_subgroup_eq [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by sorry
