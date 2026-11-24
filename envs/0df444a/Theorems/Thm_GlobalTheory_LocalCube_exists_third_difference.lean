-- Prove2me | Theorems.Thm_GlobalTheory_LocalCube_exists_third_difference
-- name    : GlobalTheory.LocalCube.exists_third_difference
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:14:09.229271+00:00
-- url     : https://prove2.me/theorems/4393505b-d504-48c6-88aa-a32b43d815ce
-- title:
--   Local Cube: exists third difference
-- statement:
--   The Local Cube construction uses the exists third difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SeriesApplyEqZeroOfFace.lean#L169-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/SeriesApplyEqZeroOfFace.lean#L169-L317

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SeriesApplyEqZeroOfFace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology Asymptotics
open scoped BigOperators Real
open GlobalTheory GlobalTheory.LocalCube
open Complex Matrix Filter Topology Asymptotics
open scoped BigOperators Real

theorem GlobalTheory.LocalCube.exists_third_difference :
    (∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧ ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ), F =O[𝓝 0] (fun z => ‖z‖ ^ 3) → (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) := by sorry
