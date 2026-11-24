-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_casimir_colOp
-- name    : GlobalTheory.Capelli.casimir_colOp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:15.896429+00:00
-- url     : https://prove2.me/theorems/090ee309-4bd1-4458-af5b-fdef100add8e
-- title:
--   Capelli: casimir col Op
-- statement:
--   The Capelli construction uses the casimir col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L251-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L251-L258

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
open GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K] {p q n : ℕ}

theorem GlobalTheory.Capelli.casimir_colOp (z : Fin p × Fin n → σ) (hz : Function.Injective z)
    (P : MvPolynomial σ K) :
    ∑ k, ∑ l, colOp K z k l (colOp K z l k P) =
      ∑ a, ∑ b, rowOp K z a b (rowOp K z b a P) +
        ((n : K) - (p : K)) • ∑ a, rowOp K z a a P := by sorry
