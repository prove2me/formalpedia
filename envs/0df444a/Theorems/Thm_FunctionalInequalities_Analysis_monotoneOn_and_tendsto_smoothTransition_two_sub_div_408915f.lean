-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_monotoneOn_and_tendsto_smoothTransition_two_sub_div_408915f
-- name    : FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:48.540446+00:00
-- url     : https://prove2.me/theorems/5d7de849-2e8e-4810-8b7c-b331547f664b
-- title:
--   Monotone Smooth-Transition Exhaustion
-- statement:
--   This formalizes the scalar exhaustion part of Lemma A.4 of Letwin (arXiv:2607.24164v1), locator Lemma A.4, p. 17.
--
--   For every $a\in\mathbb R$, define
--   $$
--   \chi_R=\operatorname{smoothTransition}(2-a/R).
--   $$
--   As a function of the positive parameter $R$, $\chi_R$ is monotone on $(0,\infty)$, and
--   $$
--   \lim_{R\to\infty}\operatorname{smoothTransition}(2-a/R)=1.
--   $$
--   The limit is expressed as convergence along the real filter `atTop` to the neighborhood of $1$.
--
--   This is a scalar monotone-exhaustion tool for cutoff constructions.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L420-L468 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div_408915f (a : ℝ) :
    MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - a / R)) (Set.Ioi 0) ∧
      Filter.Tendsto (fun R : ℝ => Real.smoothTransition (2 - a / R)) Filter.atTop (nhds 1) := by sorry
