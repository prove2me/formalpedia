-- Prove2me | Theorems.Thm_GlobalTheory_orbitAverage_exists
-- name    : GlobalTheory.orbitAverage_exists
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:07.946314+00:00
-- url     : https://prove2.me/theorems/d67c2716-77ca-4408-b250-5ce606d520f2
-- title:
--   Global Theory: orbit Average exists
-- statement:
--   The Global Theory construction uses the orbit Average exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L240-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAveragingProjection.lean#L240-L263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open GlobalTheory.OrbitAvg

theorem GlobalTheory.orbitAverage_exists : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (L : Subgroup G) (D : Submodule ℂ V),
    (∀ l ∈ L, ∀ x ∈ D, π l x ∈ D) → (∀ x ∈ D, (Set.range fun l : L => π (l : G) x).Finite) →
    ∃ P : D →ₗ[ℂ] D, (∀ x : D, (∀ l ∈ L, π l (x : V) = x) → P x = x) ∧
      (∀ x : D, ∀ l ∈ L, π l (P x : V) = P x) ∧
      ∀ x y : D, ∃ (s : Finset G) (f : G → G), s.Nonempty ∧ (∀ g ∈ s, g ∈ L) ∧
        (P x : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (x : V) ∧
        (P y : V) = (s.card : ℂ)⁻¹ • ∑ g ∈ s, π g (y : V) ∧
        Set.BijOn f (s : Set G) (s : Set G) ∧ ∀ g ∈ s, π g⁻¹ (y : V) = π (f g) (y : V) := by sorry
