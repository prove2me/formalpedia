-- Prove2me | Theorems.Thm_GlobalTheory_pderivEval_X
-- name    : GlobalTheory.pderivEval_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:46.986067+00:00
-- url     : https://prove2.me/theorems/bc709992-00da-4665-b47a-d81c20ec192a
-- title:
--   Global Theory: pderiv Eval X
-- statement:
--   The Global Theory construction uses the pderiv Eval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/PredMulSumPadicValNatFactorialAddCardLe.lean#L141-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPolynomial
variable {R σ Λ : Type*} [CommRing R]

theorem GlobalTheory.pderivEval_X (i : σ) :
    pderivEval (X i : MvPolynomial σ R) = (pderiv i).toLinearMap := by sorry
