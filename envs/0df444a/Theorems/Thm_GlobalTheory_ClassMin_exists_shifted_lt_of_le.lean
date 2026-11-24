-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_exists_shifted_lt_of_le
-- name    : GlobalTheory.ClassMin.exists_shifted_lt_of_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:39.480328+00:00
-- url     : https://prove2.me/theorems/4e52c90a-ed9e-467b-85c8-27a61356dae7
-- title:
--   Class Min: exists shifted lt of le
-- statement:
--   The Class Min construction uses the exists shifted lt of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L115-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ} {N : ℤ} {d : ℕ}

theorem GlobalTheory.ClassMin.exists_shifted_lt_of_le {g : ℕ} (hg : finrank ℤ X ≤ g) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * g * (2 : ℝ) ^ ((g : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by sorry
