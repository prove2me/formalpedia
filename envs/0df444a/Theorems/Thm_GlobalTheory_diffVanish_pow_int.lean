-- Prove2me | Theorems.Thm_GlobalTheory_diffVanish_pow_int
-- name    : GlobalTheory.diffVanish_pow_int
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:48.544182+00:00
-- url     : https://prove2.me/theorems/f2ac8b64-068c-4749-8f48-3baa1bc2bc4c
-- title:
--   Global Theory: diff Vanish pow int
-- statement:
--   The Global Theory construction uses the diff Vanish pow int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L437-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L437-L443

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

theorem GlobalTheory.diffVanish_pow_int (d : ℕ) :
    DiffVanish (d + 1) (fun t : ℤ ↦ t ^ d) ∧ ¬ DiffVanish d (fun t : ℤ ↦ t ^ d) := by sorry
