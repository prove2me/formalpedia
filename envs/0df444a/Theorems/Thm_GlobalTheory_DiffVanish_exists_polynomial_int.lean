-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_exists_polynomial_int
-- name    : GlobalTheory.DiffVanish.exists_polynomial_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:11.476927+00:00
-- url     : https://prove2.me/theorems/810d9505-f732-4cfe-bef2-68a3fd248c2e
-- title:
--   Diff Vanish: exists polynomial int
-- statement:
--   The Diff Vanish construction uses the exists polynomial int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L428-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L428-L433

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

theorem GlobalTheory.DiffVanish.exists_polynomial_int {d : ℕ} {φ : G → ℤ} (h : DiffVanish (d + 1) φ)
    (K : Type*) [Field K] [CharZero K] (a x : G) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = φ (x + n • a)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * multiDiff (fun _ : Fin d ↦ a) φ x := by sorry
