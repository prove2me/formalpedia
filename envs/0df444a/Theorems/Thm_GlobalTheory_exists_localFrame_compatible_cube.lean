-- Prove2me | Theorems.Thm_GlobalTheory_exists_localFrame_compatible_cube
-- name    : GlobalTheory.exists_localFrame_compatible_cube
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:19.685145+00:00
-- url     : https://prove2.me/theorems/90d25cb7-8a9e-4687-bbe0-ca8fba0ecdef
-- title:
--   Global Theory: exists local Frame compatible cube
-- statement:
--   The Global Theory construction uses the exists local Frame compatible cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLocalFrameCompatibleCube.lean#L9-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLocalFrameCompatibleCube.lean#L9-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLocalFrameCompatibleCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.exists_localFrame_compatible_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by sorry
