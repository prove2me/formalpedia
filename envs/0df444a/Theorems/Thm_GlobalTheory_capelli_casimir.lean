-- Prove2me | Theorems.Thm_GlobalTheory_capelli_casimir
-- name    : GlobalTheory.capelli_casimir
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:39.639737+00:00
-- url     : https://prove2.me/theorems/b74c79fe-bc2c-498c-8196-18e36bb27bef
-- title:
--   Global Theory: capelli casimir
-- statement:
--   The Global Theory construction uses the capelli casimir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L209-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L209-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
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
open Capelli

theorem GlobalTheory.capelli_casimir {K σ : Type*} [CommRing K] [DecidableEq σ] {p n : ℕ} (z : Fin p × Fin n → σ) (hz : Function.Injective z) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l)) (∑ b, X (z (b, l)) * pderiv (z (b, k)) P)) =
    (∑ a, ∑ b, ∑ k, X (z (a, k)) * pderiv (z (b, k)) (∑ l, X (z (b, l)) * pderiv (z (a, l)) P)) +
      ((n : K) - (p : K)) • ∑ w : Fin p × Fin n, X (z w) * pderiv (z w) P := by sorry
