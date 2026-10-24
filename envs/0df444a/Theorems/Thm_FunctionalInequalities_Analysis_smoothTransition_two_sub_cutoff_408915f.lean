-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_smoothTransition_two_sub_cutoff_408915f
-- name    : FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:55.629102+00:00
-- url     : https://prove2.me/theorems/76919c50-0af4-4b1e-81c2-270af85dc368
-- title:
--   Smooth Two-Scale Cutoff Profile
-- statement:
--   This formalizes the scalar part of Lemma A.4 of Letwin (arXiv:2607.24164v1), with a stronger standalone profile statement.
--
--   Define $\eta(t)=\operatorname{smoothTransition}(2-t)$. Then $\eta$ is smooth and antitone, satisfies $0\le\eta(t)\le1$, equals $1$ for $t\le1$, and equals $0$ for $t\ge2$. If $t<1$ or $t>2$, then $\eta'(t)=\eta''(t)=0$. Both $\eta'$ and $\eta''$ have compact support, and there exists $B\ge0$ such that
--
--   $$|\eta'(t)|\le B\quad\text{and}\quad|\eta''(t)|\le B\qquad(t\in\mathbb R).$$
--
--   This is reusable scalar cutoff infrastructure; it does not construct the paper’s full generator estimates.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L32-L122 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.smoothTransition_two_sub_cutoff_408915f :
    ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (2 - s)) ∧ Antitone (fun s : ℝ => Real.smoothTransition (2 - s)) ∧
      (∀ t : ℝ, 0 ≤ Real.smoothTransition (2 - t) ∧ Real.smoothTransition (2 - t) ≤ 1) ∧
      (∀ t : ℝ, t ≤ 1 → Real.smoothTransition (2 - t) = 1) ∧
      (∀ t : ℝ, 2 ≤ t → Real.smoothTransition (2 - t) = 0) ∧
      (∀ t : ℝ, t < 1 ∨ 2 < t →
        deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t = 0 ∧ deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t = 0) ∧
      HasCompactSupport (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) ∧
      HasCompactSupport (deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s)))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
        |deriv (fun s : ℝ => Real.smoothTransition (2 - s)) t| ≤ B ∧ |deriv (deriv (fun s : ℝ => Real.smoothTransition (2 - s))) t| ≤ B := by sorry
