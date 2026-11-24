-- Prove2me | Theorems.Thm_GlobalTheory_CofactorOrder_adjugate_ne_zero
-- name    : GlobalTheory.CofactorOrder.adjugate_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:14:44.348484+00:00
-- url     : https://prove2.me/theorems/f62b3ad8-ef27-4c10-a5d7-be974aa14836
-- title:
--   Cofactor Order: adjugate ne zero
-- statement:
--   The Cofactor Order construction uses the adjugate ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L63-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L63-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.CofactorOrder.adjugate_ne_zero [Nonempty n] (M : Matrix n n K)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) ≤ 1) : M.adjugate ≠ 0 := by sorry
