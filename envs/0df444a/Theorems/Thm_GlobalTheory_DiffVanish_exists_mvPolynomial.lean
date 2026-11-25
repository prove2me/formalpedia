-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_exists_mvPolynomial
-- name    : GlobalTheory.DiffVanish.exists_mvPolynomial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:16.618899+00:00
-- url     : https://prove2.me/theorems/4e017312-8bd5-4bcd-b333-a01db754caa4
-- title:
--   Diff Vanish: exists mv Polynomial
-- statement:
--   The Diff Vanish construction uses the exists mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L392-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L392-L401

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

theorem GlobalTheory.DiffVanish.exists_mvPolynomial {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → G) (x : G) : ∃ P : MvPolynomial ι K,
      P.totalDegree ≤ d ∧ (∀ n : ι → ℤ, P.eval (fun i ↦ (n i : K)) = φ (x + ∑ i, n i • g i)) ∧
      MvPolynomial.homogeneousComponent d P = diffTopPoly d g φ x ∧
      ∀ n : ι → ℤ, (MvPolynomial.homogeneousComponent d P).eval (fun i ↦ (n i : K)) =
        (d.factorial : K)⁻¹ * h.form fun _ ↦ ∑ i, n i • g i := by sorry
