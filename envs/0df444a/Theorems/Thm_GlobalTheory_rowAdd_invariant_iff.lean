-- Prove2me | Theorems.Thm_GlobalTheory_rowAdd_invariant_iff
-- name    : GlobalTheory.rowAdd_invariant_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:05.105234+00:00
-- url     : https://prove2.me/theorems/fb94152d-327b-598d-9f1e-a4c7583fb52f
-- title:
--   Global Theory: row Add invariant iff
-- statement:
--   The Global Theory construction uses the row Add invariant iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RowAddGenericRowAddTerm.lean#L81-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/RowAddGenericRowAddTerm.lean#L81-L108

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
set_option linter.unusedVariables false

theorem GlobalTheory.rowAdd_invariant_iff {K σ ι : Type*} [Field K] [CharZero K] [DecidableEq σ] [Fintype ι]
    (u w : ι → σ) (hw : Function.Injective w)
    (huw : ∀ k l, u k ≠ w l) (P : MvPolynomial σ K) :
    List.TFAE [∀ t : ℤ, bind₁ (fun s => X s + ∑ k, if s = w k then C (t : K) * X (u k) else 0) P = P,
      ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P = P,
      ∑ k, X (u k) * pderiv (w k) P = 0] := by sorry
