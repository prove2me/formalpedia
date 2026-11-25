-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPolynomialEvaluation_contDiff_mvEval
-- name    : GlobalTheory.SmoothPolynomialEvaluation.contDiff_mvEval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:03.820804+00:00
-- url     : https://prove2.me/theorems/766e6942-e86d-5f1d-ad8f-a30556ba44d0
-- title:
--   Smooth Polynomial Evaluation: cont Diff mv Eval
-- statement:
--   The Smooth Polynomial Evaluation construction uses the cont Diff mv Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SmoothPolynomialEvaluation

theorem GlobalTheory.SmoothPolynomialEvaluation.contDiff_mvEval {d : ℕ} (q : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => MvPolynomial.eval v.1 q) := by sorry
