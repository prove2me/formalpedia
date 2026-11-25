-- Prove2me | Theorems.Thm_GlobalTheory_unfolding_isFundamentalDomain
-- name    : GlobalTheory.unfolding_isFundamentalDomain
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:14.966797+00:00
-- url     : https://prove2.me/theorems/32bc6edf-43a9-400c-b925-049738e1edb5
-- title:
--   Global Theory: unfolding is Fundamental Domain
-- statement:
--   The Global Theory construction uses the unfolding is Fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L464-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EncardSmulMemLeEncardSmulInterNonempty.lean#L464-L485

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

theorem GlobalTheory.unfolding_isFundamentalDomain (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    (∀ B : Set X, NullMeasurableSet B μ → ∀ m : ℝ≥0∞,
      (∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) →
        ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ) ∧
    (∀ B : Set X, NullMeasurableSet B μ → ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ) ∧
    (Function.Surjective φ' → (∀ (k : K) (x : X), φ' k • x = k • x) →
      IsFundamentalDomain H' D' μ →
        μ D ≤ μ D' ∧ (K.FiniteIndex →
          (∃ n : ℕ, 0 < n ∧ n ∣ K.index ∧ μ D' = n * μ D ∧
            ∫⁻ x in D', u x ∂μ = n * ∫⁻ x in D, u x ∂μ) ∧
          ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ)) := by sorry
