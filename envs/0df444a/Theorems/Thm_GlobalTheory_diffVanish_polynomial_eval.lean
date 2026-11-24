-- Prove2me | Theorems.Thm_GlobalTheory_diffVanish_polynomial_eval
-- name    : GlobalTheory.diffVanish_polynomial_eval
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:01.819258+00:00
-- url     : https://prove2.me/theorems/4348a941-7808-46da-9c1f-f1ca1cd9dcea
-- title:
--   Global Theory: diff Vanish polynomial eval
-- statement:
--   The Global Theory construction uses the diff Vanish polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L279-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L279-L283

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

theorem GlobalTheory.diffVanish_polynomial_eval {R : Type*} [CommRing R] {d : ℕ} (p : Polynomial R)
    (hp : p.natDegree ≤ d) : DiffVanish (d + 1) (fun t ↦ p.eval t) := by sorry
