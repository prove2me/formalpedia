-- Prove2me | Theorems.Thm_GlobalTheory_multiDiff_map
-- name    : GlobalTheory.multiDiff_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:54.713677+00:00
-- url     : https://prove2.me/theorems/6f927471-9be4-4f06-9867-21c03f736f0c
-- title:
--   Global Theory: multi Diff map
-- statement:
--   The Global Theory construction uses the multi Diff map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L118-L120

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

theorem GlobalTheory.multiDiff_map {ι N : Type*} [Fintype ι] [AddCommGroup N] (f : M →+ N) (g : ι → G)
    (φ : G → M) : multiDiff g (f ∘ φ) = f ∘ multiDiff g φ := by sorry
