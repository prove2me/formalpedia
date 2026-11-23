-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_pow
-- name    : GlobalTheory.multiDiff_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:32.349123+00:00
-- url     : https://prove2.me/theorems/34d35470-486d-46b4-b36f-d3151e2079d6
-- title:
--   Global Theory: multi Diff pow
-- statement:
--   The Global Theory construction uses the multi Diff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L285-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L285-L287

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

theorem GlobalTheory.multiDiff_pow {R : Type*} [CommRing R] {d : ℕ} (z : Fin d → R) (y : R) :
    multiDiff z (fun t ↦ t ^ d) y = d.factorial * ∏ i, z i := by sorry
