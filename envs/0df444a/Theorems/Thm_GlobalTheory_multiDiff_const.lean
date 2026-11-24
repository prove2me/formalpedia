-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_const
-- name    : GlobalTheory.multiDiff_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:09.279231+00:00
-- url     : https://prove2.me/theorems/1c06905c-23ee-4812-8fa6-6da5c92b176e
-- title:
--   Global Theory: multi Diff const
-- statement:
--   The Global Theory construction uses the multi Diff const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L96-L103

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

theorem GlobalTheory.multiDiff_const {d : ℕ} (a : G) (φ : G → M) :
    multiDiff (fun _ : Fin d ↦ a) φ = (bwdDiff a)^[d] φ := by sorry
