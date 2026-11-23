-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_comap
-- name    : GlobalTheory.multiDiff_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:44.701841+00:00
-- url     : https://prove2.me/theorems/43822191-1163-4313-8160-70b4560bf7c6
-- title:
--   Global Theory: multi Diff comap
-- statement:
--   The Global Theory construction uses the multi Diff comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L122-L124

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

theorem GlobalTheory.multiDiff_comap {ι H : Type*} [Fintype ι] [AddCommGroup H] (f : H →+ G) (g : ι → H)
    (φ : G → M) : multiDiff g (φ ∘ f) = multiDiff (f ∘ g) φ ∘ f := by sorry
