-- Prove2me | Theorems.Thm_GlobalTheory_setLIntegral_eq_index_map_mul
-- name    : GlobalTheory.setLIntegral_eq_index_map_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:42.005195+00:00
-- url     : https://prove2.me/theorems/d9f53bc4-8169-4772-8010-03c16474fc87
-- title:
--   Global Theory: set LIntegral eq index map mul
-- statement:
--   The Global Theory construction uses the set LIntegral eq index map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L393-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L393-L406

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
variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}
variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]
variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}

theorem GlobalTheory.setLIntegral_eq_index_map_mul [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ((K.map φ).index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by sorry
