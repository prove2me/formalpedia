-- Prove2me | Theorems.Thm_GlobalTheory_CofactorOrder_ker_eq_bot_of_det
-- name    : GlobalTheory.CofactorOrder.ker_eq_bot_of_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:39.70418+00:00
-- url     : https://prove2.me/theorems/4c216646-e103-4315-9c81-6668ed598f54
-- title:
--   Cofactor Order: ker eq bot of det
-- statement:
--   The Cofactor Order construction uses the ker eq bot of det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L26-L30

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

theorem GlobalTheory.CofactorOrder.ker_eq_bot_of_det {P : Matrix n n K} (hP : P.det = 1) :
    LinearMap.ker P.mulVecLin = ⊥ := by sorry
