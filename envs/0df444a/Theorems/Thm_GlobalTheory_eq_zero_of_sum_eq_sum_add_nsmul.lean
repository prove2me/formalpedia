-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_sum_eq_sum_add_nsmul
-- name    : GlobalTheory.eq_zero_of_sum_eq_sum_add_nsmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:20.463027+00:00
-- url     : https://prove2.me/theorems/159af26a-d89d-46aa-893f-973d0b63e290
-- title:
--   Global Theory: eq zero of sum eq sum add nsmul
-- statement:
--   The Global Theory construction uses the eq zero of sum eq sum add nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisUniqueMinAndSumsSeparated.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisUniqueMinAndSumsSeparated.lean#L8-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisUniqueMinAndSumsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.eq_zero_of_sum_eq_sum_add_nsmul {X : Type*} [AddCommGroup X] {ι : Type*}
    (e : Basis ι ℤ X) {C : ℝ} (hC : 0 ≤ C) {N' D k : ℕ} (hN' : 2 * (D : ℝ) * C < N') (hk : k ≤ D)
    (α β : Fin k → X) (hα : ∀ j i, |(e.repr (α j) i : ℝ)| ≤ C)
    (hβ : ∀ j i, |(e.repr (β j) i : ℝ)| ≤ C) (w : X)
    (h : ∑ j, α j = ∑ j, β j + N' • w) : w = 0 := by sorry
