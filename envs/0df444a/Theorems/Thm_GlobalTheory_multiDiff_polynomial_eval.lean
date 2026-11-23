-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_polynomial_eval
-- name    : GlobalTheory.multiDiff_polynomial_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:47.743073+00:00
-- url     : https://prove2.me/theorems/041923b5-e467-4c0b-8c3f-01a793f7e7e9
-- title:
--   Global Theory: multi Diff polynomial eval
-- statement:
--   The Global Theory construction uses the multi Diff polynomial eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L248-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L248-L277

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

theorem GlobalTheory.multiDiff_polynomial_eval {R : Type*} [CommRing R] {d : ℕ} (z : Fin d → R)
    (p : Polynomial R) (hp : p.natDegree ≤ d) (y : R) :
    multiDiff z (fun t ↦ p.eval t) y = d.factorial * p.coeff d * ∏ i, z i := by sorry
