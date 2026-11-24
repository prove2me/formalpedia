-- Prove2me | Theorems.Thm_GlobalTheory_CofactorOrder_diag_case
-- name    : GlobalTheory.CofactorOrder.diag_case
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:14:58.317596+00:00
-- url     : https://prove2.me/theorems/343d884c-d005-4db8-9330-6c5453d35395
-- title:
--   Cofactor Order: diag case
-- statement:
--   The Cofactor Order construction uses the diag case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L102-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L102-L189

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

theorem GlobalTheory.CofactorOrder.diag_case [Nonempty n] (Θ : Matrix n n K[X]) (D : n → K)
    [DecidablePred fun i => D i = 0] (hD : (Θ.map fun p => p.coeff 0) = diagonal D)
    (H : ∀ x0 x1 : Fin (1 + 1) → n → K, (∀ j, (Θ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Θ.map fun p => p.coeff 1).mulVec (x0 j) + (Θ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0) :
    ∃ b c, ¬ (X : K[X]) ^ (Fintype.card {i // D i = 0} + 1) ∣ Θ.adjugate b c := by sorry
