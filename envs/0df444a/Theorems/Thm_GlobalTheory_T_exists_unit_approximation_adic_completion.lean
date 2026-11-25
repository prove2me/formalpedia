-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unit_approximation_adic_completion
-- name    : GlobalTheory.T.exists_unit_approximation_adic_completion
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:11.02005+00:00
-- url     : https://prove2.me/theorems/55a98f01-b5c7-438e-b54c-1dfd9fa828cd
-- title:
--   T: exists unit approximation adic completion
-- statement:
--   The T construction uses the exists unit approximation adic completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitApproximationAdicCompletionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitApproximationAdicCompletionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitApproximationAdicCompletion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitApproximationAdicCompletionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unit_approximation_adic_completion : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M] [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N] (φ : M →ₐ[A] N), (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) → (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) → ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧ ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by sorry
