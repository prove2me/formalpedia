-- Prove2me | Theorems.Thm_GlobalTheory_T_local_max_principle_weighted_finiteType_int
-- name    : GlobalTheory.T.local_max_principle_weighted_finiteType_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:03.663478+00:00
-- url     : https://prove2.me/theorems/437be061-abf0-4dc4-b572-a43fc0a882a9
-- title:
--   T: local max principle weighted finite Type int
-- statement:
--   The T construction uses the local max principle weighted finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeIntStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalMaxPrincipleWeightedFiniteTypeIntStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalMaxPrincipleWeightedFiniteTypeIntStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_max_principle_weighted_finiteType_int : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B], (letI : TopologicalSpace (B →+* ℂ) := TopologicalSpace.induced (fun x : B →+* ℂ => (x : B → ℂ)) inferInstance; ∀ (ψ : (B →+* ℂ) → ℝ), Continuous ψ → ∀ s : B, s ≠ 0 → ∀ (x₀ : B →+* ℂ) (δ : ℝ), 0 < δ → ∃ (W K : Set (B →+* ℂ)), W ∈ nhds x₀ ∧ IsCompact K ∧ (∀ x ∈ K, x s ≠ 0) ∧ ∀ (N : ℕ) (f : B) (R : ℝ), (∀ x ∈ K, ‖x f‖ * Real.exp (-(N * ψ x)) ≤ R) → ∀ y ∈ W, ‖y f‖ * Real.exp (-(N * ψ y)) ≤ Real.exp (δ * N) * R) := by sorry
