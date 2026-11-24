-- Prove2me | Theorems.Thm_GlobalTheory_powerSeries_generic_relation_chain
-- name    : GlobalTheory.powerSeries_generic_relation_chain
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:23.127247+00:00
-- url     : https://prove2.me/theorems/8ac81a5d-1ec2-4424-96a9-5f565acd6f3e
-- title:
--   Global Theory: power Series generic relation chain
-- statement:
--   The Global Theory construction uses the power Series generic relation chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PowerSeriesGenericRelationChain.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PowerSeriesGenericRelationChain.lean#L5-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PowerSeriesGenericRelationChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.powerSeries_generic_relation_chain :
    ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by sorry
