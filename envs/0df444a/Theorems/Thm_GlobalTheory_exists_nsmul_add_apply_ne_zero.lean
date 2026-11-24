-- Prove2me | Theorems.Thm_GlobalTheory_exists_nsmul_add_apply_ne_zero
-- name    : GlobalTheory.exists_nsmul_add_apply_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:26.486314+00:00
-- url     : https://prove2.me/theorems/90ca16b5-caf5-4333-82c4-e6155dd49dfb
-- title:
--   Global Theory: exists nsmul add apply ne zero
-- statement:
--   The Global Theory construction uses the exists nsmul add apply ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L115-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfEvalGridEqZeroOfTotalDegreeLe.lean#L115-L142

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

theorem GlobalTheory.exists_nsmul_add_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] (l : ∀ j, V →+ W j)
    (v w : V) :
    ∃ c : ℕ, c ≤ Fintype.card ι ∧ ∀ j, l j v ≠ 0 ∨ l j w ≠ 0 → l j (c • w + v) ≠ 0 := by sorry
