-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_doubling
-- name    : GlobalTheory.CubeFace.doubling
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:28:04.99643+00:00
-- url     : https://prove2.me/theorems/4a582b3f-2059-4905-8581-bfbe82674db1
-- title:
--   Cube Face: doubling
-- statement:
--   The Cube Face construction uses the doubling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L238-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L238-L380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
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
open GlobalTheory.CubeFace
variable {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ)
  (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
  (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
  (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
  (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ)
  (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
  (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
  (hTT : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
    (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
    T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
      T j' x)
  (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
  (hWp : ∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i)
  (hTp : ∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x)
  (i₀ : ι) (h0 : (0 : Fin g → ℂ) ∈ W i₀)
include hW hcov hc0 hcc hT hT0 hTT hΛ hWp hTp h0

theorem GlobalTheory.CubeFace.doubling (x : Fin 3 → Fin g → ℂ)
    (hx : ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W i₀)
    (hx' : ∀ I : Finset (Fin 3), ∑ b ∈ I, (-x) b ∈ W i₀)
    (hx'' : ∀ I : Finset (Fin 3), ∑ b ∈ I, ((2 : ℂ) • x) b ∈ W i₀) :
    T (fun _ => i₀) ((2 : ℂ) • x) * (∏ I : Finset (Fin 3),
      T (fun _ => i₀) ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^
        ((-1 : ℤ) ^ (3 - I.card))) * T (fun _ => i₀) 0 ^ 3 =
      T (fun _ => i₀) x ^ 3 * T (fun _ => i₀) (-x) := by sorry
