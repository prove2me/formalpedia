-- Prove2me | Theorems.Thm_GlobalTheory_setLAverage_eq_of_range_toPermHom
-- name    : GlobalTheory.setLAverage_eq_of_range_toPermHom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:03.038145+00:00
-- url     : https://prove2.me/theorems/e91a0854-df1b-49cf-a6e4-4ee896243b99
-- title:
--   Global Theory: set LAverage eq of range to Perm Hom
-- statement:
--   The Global Theory construction uses the set LAverage eq of range to Perm Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L509-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L509-L515

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

theorem GlobalTheory.setLAverage_eq_of_range_toPermHom [K.FiniteIndex]
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hD' : IsFundamentalDomain (MulAction.toPermHom K X).range D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by sorry
