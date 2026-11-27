-- Prove2me | Theorems.Thm_GlobalTheory_setAverage_eq_of_surjective
-- name    : GlobalTheory.setAverage_eq_of_surjective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:06.048393+00:00
-- url     : https://prove2.me/theorems/8c531ff7-e652-4866-8391-28286604a9b5
-- title:
--   Global Theory: set Average eq of surjective
-- statement:
--   The Global Theory construction uses the set Average eq of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L445-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L445-L462

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

theorem GlobalTheory.setAverage_eq_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (IntegrableOn f D' μ ↔ IntegrableOn f D μ) ∧
      ∫ x in D', f x ∂μ = ((K.map φ).index : ℝ) • ∫ x in D, f x ∂μ ∧
      ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by sorry
