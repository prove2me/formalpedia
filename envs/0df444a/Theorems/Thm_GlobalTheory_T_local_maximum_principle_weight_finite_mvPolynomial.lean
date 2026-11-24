-- Prove2me | Theorems.Thm_GlobalTheory_T_local_maximum_principle_weight_finite_mvPolynomial
-- name    : GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:41.053585+00:00
-- url     : https://prove2.me/theorems/163465f2-eb56-480a-96f6-14af8f89e146
-- title:
--   T: local maximum principle weight finite mv Polynomial
-- statement:
--   The T construction uses the local maximum principle weight finite mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaximumPrincipleWeightFiniteMvPolynomialStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaximumPrincipleWeightFiniteMvPolynomialStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaximumPrincipleWeightFiniteMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaximumPrincipleWeightFiniteMvPolynomialStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_maximum_principle_weight_finite_mvPolynomial : ∀ (d : ℕ) (B : Type) [CommRing B] [IsDomain B] [Algebra (MvPolynomial (Fin d) ℚ) B] [Module.Finite (MvPolynomial (Fin d) ℚ) B], Function.Injective (algebraMap (MvPolynomial (Fin d) ℚ) B) → (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by sorry
