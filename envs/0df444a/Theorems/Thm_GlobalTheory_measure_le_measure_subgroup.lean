-- Prove2me | Theorems.Thm_GlobalTheory_measure_le_measure_subgroup
-- name    : GlobalTheory.measure_le_measure_subgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:34.291877+00:00
-- url     : https://prove2.me/theorems/dc05ffc9-e53e-4f46-a605-31c117f7fb1a
-- title:
--   Global Theory: measure le measure subgroup
-- statement:
--   The Global Theory construction uses the measure le measure subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L257-L260

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

theorem GlobalTheory.measure_le_measure_subgroup (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) : μ D ≤ μ D' := by sorry
