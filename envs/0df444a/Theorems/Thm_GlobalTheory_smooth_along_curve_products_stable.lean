-- Prove2me | Theorems.Thm_GlobalTheory_smooth_along_curve_products_stable
-- name    : GlobalTheory.smooth_along_curve_products_stable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:31.409807+00:00
-- url     : https://prove2.me/theorems/4643bef7-99aa-4eeb-957f-3eefc4289b13
-- title:
--   Global Theory: smooth along curve products stable
-- statement:
--   The Global Theory construction uses the smooth along curve products stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStable.lean#L209-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStable.lean#L209-L229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory
open scoped ContDiff

theorem GlobalTheory.smooth_along_curve_products_stable : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by sorry
