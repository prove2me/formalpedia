-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_408915f
-- name    : FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:18.437167+00:00
-- url     : https://prove2.me/theorems/78d866ad-ec97-46c9-800a-558e945731b6
-- title:
--   Smooth Compact Majorant for the Cutoff Curvature
-- statement:
--   This formalizes a scalar component of Lemma A.4 of Letwin (arXiv:2607.24164v1).
--
--   For $\eta(t)=\operatorname{smoothTransition}(2-t)$, there exists a smooth compactly supported function $w:\mathbb R\to\mathbb R$ such that $w\ge0$, $w(t)=0$ whenever $t\le0$ or $3\le t$, and
--
--   $$|\eta''(t)|\le w(t)\qquad(t\in\mathbb R).$$
--
--   The function $w$ is a technical compact majorant for the second derivative of the scalar cutoff.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L124-L192 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.exists_majorant_abs_deriv_deriv_smoothTransition_two_sub_408915f :
    ∃ w : ℝ → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧ (∀ t, 0 ≤ w t) ∧
      (∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) ∧
      ∀ t, |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ w t := by sorry
