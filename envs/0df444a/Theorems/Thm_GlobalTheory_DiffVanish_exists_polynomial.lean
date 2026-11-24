-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_exists_polynomial
-- name    : GlobalTheory.DiffVanish.exists_polynomial
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:16.441035+00:00
-- url     : https://prove2.me/theorems/3dbd9dc1-dd40-4e13-9132-6bf276ab89db
-- title:
--   Diff Vanish: exists polynomial
-- statement:
--   The Diff Vanish construction uses the exists polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L403-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L403-L426

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

theorem GlobalTheory.DiffVanish.exists_polynomial {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) (a x : G) :
    ∃ p : Polynomial K, p.natDegree ≤ d ∧ (∀ n : ℤ, p.eval (n : K) = φ (x + n • a)) ∧
      p.coeff d = (d.factorial : K)⁻¹ * multiDiff (fun _ : Fin d ↦ a) φ x := by sorry
