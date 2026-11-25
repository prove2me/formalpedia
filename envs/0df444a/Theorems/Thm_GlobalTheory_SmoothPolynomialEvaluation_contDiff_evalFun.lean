-- Prove2me | Theorems.Thm_GlobalTheory_SmoothPolynomialEvaluation_contDiff_evalFun
-- name    : GlobalTheory.SmoothPolynomialEvaluation.contDiff_evalFun
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:25.424809+00:00
-- url     : https://prove2.me/theorems/99df97bb-6fdc-4220-8f06-7978de49a00d
-- title:
--   Smooth Polynomial Evaluation: cont Diff eval Fun
-- statement:
--   The Smooth Polynomial Evaluation construction uses the cont Diff eval Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ContDiffEvalFun.lean#L19-L30

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

theorem GlobalTheory.SmoothPolynomialEvaluation.contDiff_evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (evalFun p) := by sorry
