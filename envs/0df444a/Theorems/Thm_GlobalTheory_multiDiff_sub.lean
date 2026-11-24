-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_sub
-- name    : GlobalTheory.multiDiff_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:00.618837+00:00
-- url     : https://prove2.me/theorems/e85b1b23-55b6-41bd-beac-934f58a0b954
-- title:
--   Global Theory: multi Diff sub
-- statement:
--   The Global Theory construction uses the multi Diff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L114-L116

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

theorem GlobalTheory.multiDiff_sub {ι : Type*} [Fintype ι] (g : ι → G) (φ ψ : G → M) :
    multiDiff g (φ - ψ) = multiDiff g φ - multiDiff g ψ := by sorry
