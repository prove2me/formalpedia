-- Prove2me | Theorems.Thm_GlobalTheory_derivative_rowAddGeneric
-- name    : GlobalTheory.derivative_rowAddGeneric
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:07.195729+00:00
-- url     : https://prove2.me/theorems/766db2ac-f063-4c98-ab60-5cdceb9f79c4
-- title:
--   Global Theory: derivative row Add Generic
-- statement:
--   The Global Theory construction uses the derivative row Add Generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RowAddGenericRowAddTerm.lean#L54-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RowAddGenericRowAddTerm.lean#L54-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_RowAddGenericRowAddTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]

theorem GlobalTheory.derivative_rowAddGeneric (u w : ι → σ) (huw : ∀ k l, u k ≠ w l)
    (P : MvPolynomial σ K) :
    Polynomial.derivative (rowAddGeneric u w P) =
      rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P) := by sorry
