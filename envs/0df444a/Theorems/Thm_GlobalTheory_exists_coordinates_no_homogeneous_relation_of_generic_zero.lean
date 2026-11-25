-- Prove2me | Theorems.Thm_GlobalTheory_exists_coordinates_no_homogeneous_relation_of_generic_zero
-- name    : GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:57:03.093071+00:00
-- url     : https://prove2.me/theorems/5ade1977-54d0-4239-8eb6-400769b4c197
-- title:
--   Global Theory: exists coordinates no homogeneous relation of generic zero
-- statement:
--   The Global Theory construction uses the exists coordinates no homogeneous relation of generic zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoordsNoHomogeneousRelationGenericHyperpla.lean#L60-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoordsNoHomogeneousRelationGenericHyperpla.lean#L60-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsAlgebraicIndependentRatiosOfGenericZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoordsNoHomogeneousRelationGenericHyperpla
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero :
    ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ),
    (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 →
    (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N,
      ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d →
        MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by sorry
