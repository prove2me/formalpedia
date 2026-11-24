-- Prove2me | Theorems.Thm_GlobalTheory_Chow_eq_zero_of_mem_elimIdeal_of_forall_meets
-- name    : GlobalTheory.Chow.eq_zero_of_mem_elimIdeal_of_forall_meets
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:51.870435+00:00
-- url     : https://prove2.me/theorems/1d4c327b-db3b-485a-a015-dbded21dd5cc
-- title:
--   Chow: eq zero of mem elim Ideal of forall meets
-- statement:
--   The Chow construction uses the eq zero of mem elim Ideal of forall meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeSaturationGenericHyperplaneSection.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeSaturationGenericHyperplaneSection.lean#L47-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeSaturationGenericHyperplaneSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow

theorem GlobalTheory.Chow.eq_zero_of_mem_elimIdeal_of_forall_meets {K : Type} [Field K] {N : ℕ}
    {P : Ideal (MvPolynomial (Fin N) K)}
    (hP : ∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K,
      y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0)
    {f : MvPolynomial (Unit × Fin N) K} (hf : f ∈ elimIdeal Unit P) : f = 0 := by sorry
