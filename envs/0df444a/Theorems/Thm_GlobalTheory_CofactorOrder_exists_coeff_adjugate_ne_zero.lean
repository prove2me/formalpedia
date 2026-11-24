-- Prove2me | Theorems.Thm_GlobalTheory_CofactorOrder_exists_coeff_adjugate_ne_zero
-- name    : GlobalTheory.CofactorOrder.exists_coeff_adjugate_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:02:36.095681+00:00
-- url     : https://prove2.me/theorems/447260be-9255-4772-a73a-dd92eb35b65f
-- title:
--   Cofactor Order: exists coeff adjugate ne zero
-- statement:
--   The Cofactor Order construction uses the exists coeff adjugate ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L81-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L81-L94

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

theorem GlobalTheory.CofactorOrder.exists_coeff_adjugate_ne_zero [Nonempty n] (Ψ : Matrix n n K[X])
    (h : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ 1) :
    ∃ b c, ¬ (X : K[X]) ∣ Ψ.adjugate b c := by sorry
