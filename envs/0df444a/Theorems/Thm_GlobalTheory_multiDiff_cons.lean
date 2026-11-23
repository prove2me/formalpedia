-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_cons
-- name    : GlobalTheory.multiDiff_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:25.581503+00:00
-- url     : https://prove2.me/theorems/655853b9-f626-4806-859a-5c0617d72eff
-- title:
--   Global Theory: multi Diff cons
-- statement:
--   The Global Theory construction uses the multi Diff cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L87-L89

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

theorem GlobalTheory.multiDiff_cons {d : ℕ} (a : G) (g : Fin d → G) (φ : G → M) :
    multiDiff (Fin.cons a g : Fin (d + 1) → G) φ = bwdDiff a (multiDiff g φ) := by sorry
