-- Prove2me | Theorems.Thm_GlobalTheory_exists_mvPolynomial_of_iteratedBackwardDifferenceVanish
-- name    : GlobalTheory.exists_mvPolynomial_of_iteratedBackwardDifferenceVanish
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:23.134423+00:00
-- url     : https://prove2.me/theorems/78d9d345-c7e4-46ce-9cfb-f886a39ee2f1
-- title:
--   Global Theory: exists mv Polynomial of iterated Backward Difference Vanish
-- statement:
--   The Global Theory construction uses the exists mv Polynomial of iterated Backward Difference Vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L371-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L371-L390

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]

theorem GlobalTheory.exists_mvPolynomial_of_iteratedBackwardDifferenceVanish {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → G) (d : ℕ) : ∀ φ : G → K, DiffVanish (d + 1) φ → ∃ P : MvPolynomial ι K,
      P.totalDegree ≤ d ∧ (∀ n : ι → ℤ, P.eval (fun i ↦ (n i : K)) = φ (∑ i, n i • g i)) ∧
      MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ 0 := by sorry
