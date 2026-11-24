-- Prove2me | Theorems.Thm_GlobalTheory_diffElt_sub_sum_mem
-- name    : GlobalTheory.diffElt_sub_sum_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:17.868803+00:00
-- url     : https://prove2.me/theorems/2a188248-f67d-4aac-9742-4f6255466ff2
-- title:
--   Global Theory: diff Elt sub sum mem
-- statement:
--   The Global Theory construction uses the diff Elt sub sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L303-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L303-L311

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

theorem GlobalTheory.diffElt_sub_sum_mem {ι : Type*} (s : Finset ι) (g : ι → G) (x : G) :
    diffElt (x - ∑ i ∈ s, g i) - (diffElt x - ∑ i ∈ s, diffElt (g i)) ∈ diffIdeal G ^ 2 := by sorry
