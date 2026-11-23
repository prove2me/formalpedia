-- Prove2me | Theorems.Thm_GlobalTheory_shiftAct_diffElt
-- name    : GlobalTheory.shiftAct_diffElt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:46.300735+00:00
-- url     : https://prove2.me/theorems/986e6c38-a795-40fa-9fa6-f50b985bb8ae
-- title:
--   Global Theory: shift Act diff Elt
-- statement:
--   The Global Theory construction uses the shift Act diff Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L42-L44

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

theorem GlobalTheory.shiftAct_diffElt (g : G) (φ : G → M) : shiftAct G M (diffElt g) φ = bwdDiff g φ := by sorry
