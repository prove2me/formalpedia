-- Prove2me | Theorems.Thm_GlobalTheory_setLAverage_subgroup_eq
-- name    : GlobalTheory.setLAverage_subgroup_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:37.815749+00:00
-- url     : https://prove2.me/theorems/cfb4b575-fecf-4c18-ac6d-dcd3599c782f
-- title:
--   Global Theory: set LAverage subgroup eq
-- statement:
--   The Global Theory construction uses the set LAverage subgroup eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L246-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L246-L253

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

theorem GlobalTheory.setLAverage_subgroup_eq [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by sorry
