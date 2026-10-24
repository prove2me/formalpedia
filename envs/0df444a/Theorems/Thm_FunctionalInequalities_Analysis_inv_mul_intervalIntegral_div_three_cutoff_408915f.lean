-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inv_mul_intervalIntegral_div_three_cutoff_408915f
-- name    : FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:30.375121+00:00
-- url     : https://prove2.me/theorems/37ff6ad0-733a-483b-a9fa-7fb79f75cd53
-- title:
--   Tail Primitive of a Compactly Supported Cutoff
-- statement:
--   This formalizes Lemma A.4 of Letwin (arXiv:2607.24164v1), locator Lemma A.4, p. 17, for its scalar tail primitive.
--
--   Let $w:\mathbb R\to\mathbb R$ be smooth, nonnegative everywhere, and zero whenever $t\le0$ or $t\ge3$. Let $R>0$ and define
--   $$
--   q_R(t)=R^{-1}\int_{t/R}^{3}w(s)\,ds.
--   $$
--   Then $q_R$ is smooth,
--   $$
--   q_R'(t)=-R^{-2}w(t/R),
--   $$
--   $0\le q_R(t)$ for every $t$, and
--   $$
--   q_R(t)\le R^{-1}\int_0^3w(s)\,ds.
--   $$
--   Finally, $q_R(t)=0$ whenever $3R\le t$.
--
--   This scalar profile is a reusable cutoff component for noncompact integration by parts.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L234-L377 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.inv_mul_intervalIntegral_div_three_cutoff_408915f {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (hw0 : ∀ t, 0 ≤ w t) (hws : ∀ t, t ≤ 0 ∨ 3 ≤ t → w t = 0) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun t => R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, deriv (fun t => R⁻¹ * ∫ s in t / R..3, w s) t = -((R ^ 2)⁻¹ * w (t / R))) ∧
      (∀ t, 0 ≤ R⁻¹ * ∫ s in t / R..3, w s) ∧
      (∀ t, R⁻¹ * ∫ s in t / R..3, w s ≤ R⁻¹ * ∫ s in (0 : ℝ)..3, w s) ∧
      (∀ t, 3 * R ≤ t → R⁻¹ * ∫ s in t / R..3, w s = 0) := by sorry
