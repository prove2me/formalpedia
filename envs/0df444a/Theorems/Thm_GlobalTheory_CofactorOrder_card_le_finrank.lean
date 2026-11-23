-- Prove2me | Theorems.Thm_GlobalTheory_CofactorOrder_card_le_finrank
-- name    : GlobalTheory.CofactorOrder.card_le_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:36.430555+00:00
-- url     : https://prove2.me/theorems/9d17eaaf-353a-4599-9519-873d3042bc4f
-- title:
--   Cofactor Order: card le finrank
-- statement:
--   The Cofactor Order construction uses the card le finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L32-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L32-L61

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

theorem GlobalTheory.CofactorOrder.card_le_finrank {M P Q : Matrix n n K} {D : n → K} [DecidablePred fun i => D i = 0]
    (hP : P.det = 1) (hQ : Q.det = 1) (h : P * M * Q = diagonal D) :
    Fintype.card {i // D i = 0} ≤ Module.finrank K (LinearMap.ker M.mulVecLin) := by sorry
