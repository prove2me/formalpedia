-- Prove2me | Theorems.Thm_GlobalTheory_measure_le_measure_of_range_toPermHom
-- name    : GlobalTheory.measure_le_measure_of_range_toPermHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:23.62995+00:00
-- url     : https://prove2.me/theorems/93a83515-f4b2-4867-a0e6-f16361ce1dba
-- title:
--   Global Theory: measure le measure of range to Perm Hom
-- statement:
--   The Global Theory construction uses the measure le measure of range to Perm Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L503-L507
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L503-L507

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
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {B D D' : Set X}
  {K : Subgroup G}

theorem GlobalTheory.measure_le_measure_of_range_toPermHom
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hD' : IsFundamentalDomain (MulAction.toPermHom K X).range D' μ) : μ D ≤ μ D' := by sorry
