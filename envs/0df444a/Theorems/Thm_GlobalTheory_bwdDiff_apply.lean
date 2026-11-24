-- Prove2me | Theorems.Thm_GlobalTheory_bwdDiff_apply
-- name    : GlobalTheory.bwdDiff_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:56.995812+00:00
-- url     : https://prove2.me/theorems/f901c33f-1e5c-4cc3-a967-20e2b5b4a4fc
-- title:
--   Global Theory: bwd Diff apply
-- statement:
--   The Global Theory construction uses the bwd Diff apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L18-L18

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

theorem GlobalTheory.bwdDiff_apply (g : G) (φ : G → M) (x : G) : bwdDiff g φ x = φ x - φ (x - g) := by sorry
