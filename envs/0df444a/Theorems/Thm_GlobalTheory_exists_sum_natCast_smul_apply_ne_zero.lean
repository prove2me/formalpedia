-- Prove2me | Theorems.Thm_GlobalTheory_exists_sum_natCast_smul_apply_ne_zero
-- name    : GlobalTheory.exists_sum_natCast_smul_apply_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:00.742747+00:00
-- url     : https://prove2.me/theorems/cc87dab1-bd8e-5fca-b584-151942ca0d3b
-- title:
--   Global Theory: exists sum nat Cast smul apply ne zero
-- statement:
--   The Global Theory construction uses the exists sum nat Cast smul apply ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L174-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]
variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]

theorem GlobalTheory.exists_sum_natCast_smul_apply_ne_zero [Fintype κ]
    (l : ∀ j, V →ₗ[K] W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, (c k : K) • s k) ≠ 0 := by sorry
