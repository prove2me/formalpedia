-- Prove2me | Theorems.Thm_GlobalTheory_GaussCoset_summable_gaussian_coset
-- name    : GlobalTheory.GaussCoset.summable_gaussian_coset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:49.539253+00:00
-- url     : https://prove2.me/theorems/6e4c198f-38b0-4b6d-aac9-314292241611
-- title:
--   Gauss Coset: summable gaussian coset
-- statement:
--   The Gauss Coset construction uses the summable gaussian coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L72-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SummableGaussianCoset.lean#L72-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SummableGaussianCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.GaussCoset

theorem GlobalTheory.GaussCoset.summable_gaussian_coset : ∀ (G V : Type) [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (Γ U : AddSubgroup G), (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U ∧ ‖p g‖ ≤ R}.Finite) → ∀ (c : ℝ), 0 < c → ∀ (R : ℝ) (w : G) (y : V), Summable fun g : Γ => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w) := by sorry
