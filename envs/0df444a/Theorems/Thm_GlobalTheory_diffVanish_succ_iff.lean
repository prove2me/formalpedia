-- Prove2me | Theorems.Thm_GlobalTheory_diffVanish_succ_iff
-- name    : GlobalTheory.diffVanish_succ_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:54.053823+00:00
-- url     : https://prove2.me/theorems/b86c8f39-26dc-4e9b-8c14-37f87c458087
-- title:
--   Global Theory: diff Vanish succ iff
-- statement:
--   The Global Theory construction uses the diff Vanish succ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L188-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L188-L191

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
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem GlobalTheory.diffVanish_succ_iff {n : ℕ} {φ : G → M} :
    DiffVanish (n + 1) φ ↔ ∀ a, DiffVanish n (bwdDiff a φ) := by sorry
