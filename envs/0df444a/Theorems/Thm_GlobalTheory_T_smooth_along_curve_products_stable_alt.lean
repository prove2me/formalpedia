-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_along_curve_products_stable_alt
-- name    : GlobalTheory.T.smooth_along_curve_products_stable_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:57:44.293219+00:00
-- url     : https://prove2.me/theorems/89d46f74-8db1-4360-8299-c96a578d6e1b
-- title:
--   T: smooth along curve products stable alt
-- statement:
--   The T construction uses the smooth along curve products stable alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmoothAlongCurveProductsStableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothAlongCurveProductsStableStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smooth_along_curve_products_stable_alt : ∀ (G : Type) [Group G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (P : Type) (A : Set P) (e : P → ℝ → G) (v : K), (∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod v) → (∀ p ∈ A, ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (deriv (fun r : ℝ => ρ (e p r) v) 0)) ∧ (∀ (m : ℕ) (qs : Fin m → P) (r : Fin m → ℝ), (∀ i, qs i ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => ρ (List.ofFn fun i => e (ps i) (t i)).prod (ρ (List.ofFn fun i => e (qs i) (r i)).prod v)) ∧ ∀ l : List P, (∀ p ∈ l, p ∈ A) → ∀ (k : ℕ) (ps : Fin k → P), (∀ i, ps i ∈ A) → ContDiff ℝ ∞ fun t : Fin k → ℝ => l.foldr (fun p w => deriv (fun r : ℝ => ρ (e p r) w) 0) (ρ (List.ofFn fun i => e (ps i) (t i)).prod v) := by sorry
