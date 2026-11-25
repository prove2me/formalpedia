-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_coords_no_homogeneous_relation_generic_hyperplanes
-- name    : GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:18.963804+00:00
-- url     : https://prove2.me/theorems/f072c3f2-5a1f-485d-a2f7-2d934eef59bb
-- title:
--   T: exists coords no homogeneous relation generic hyperplanes
-- statement:
--   The T construction uses the exists coords no homogeneous relation generic hyperplanes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperpla
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ), (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 → (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N, ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d → MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by sorry
