-- Prove2me | Theorems.Thm_GlobalTheory_CubeFrame_exists_global_frame
-- name    : GlobalTheory.CubeFrame.exists_global_frame
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:27.828916+00:00
-- url     : https://prove2.me/theorems/0465e80a-2c18-4634-bc25-b7cbf7513001
-- title:
--   Cube Frame: exists global frame
-- statement:
--   The Cube Frame construction uses the exists global frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L338-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsGlobalFrameOfLocal.lean#L338-L344

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal
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
open GlobalTheory GlobalTheory.CubeFrame
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {ι : Type} {W : ι → Set E} {c : ι → ι → E → ℂ}
  {T : (Finset (Fin 3) → ι) → (Fin 3 → E) → ℂ}

theorem GlobalTheory.CubeFrame.exists_global_frame :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → (∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) ∧ ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by sorry
