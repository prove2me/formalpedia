-- Prove2me | Theorems.Thm_GlobalTheory_exists_sum_nsmul_apply_ne_zero_finset
-- name    : GlobalTheory.exists_sum_nsmul_apply_ne_zero_finset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:24.077246+00:00
-- url     : https://prove2.me/theorems/e8d37a0d-9bff-4c6f-acb8-d5776813a249
-- title:
--   Global Theory: exists sum nsmul apply ne zero finset
-- statement:
--   The Global Theory construction uses the exists sum nsmul apply ne zero finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L144-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L144-L164

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

theorem GlobalTheory.exists_sum_nsmul_apply_ne_zero_finset [∀ j, IsAddTorsionFree (W j)]
    (l : ∀ j, V →+ W j) (s : κ → V) (t : Finset κ) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧
      ∀ j, (∃ k ∈ t, l j (s k) ≠ 0) → l j (∑ k ∈ t, c k • s k) ≠ 0 := by sorry
