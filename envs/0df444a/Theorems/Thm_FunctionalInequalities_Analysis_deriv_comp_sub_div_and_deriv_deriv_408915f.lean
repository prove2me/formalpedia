-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_deriv_comp_sub_div_and_deriv_deriv_408915f
-- name    : FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:33.59978+00:00
-- url     : https://prove2.me/theorems/a37ca1b6-16e7-4cdd-8931-1415096bdbf3
-- title:
--   Affine Rescaling Of First And Second Derivatives
-- statement:
--   This formalizes the affine rescaling identities cited from Letwin (arXiv:2607.24164v1), locator Lemma A.4, with the reviewed relation recorded as stronger.
--
--   Let $f:\mathbb R\to\mathbb R$ and let $c,R,t\in\mathbb R$. Define $g(s)=f((s-c)/R)$. Then, using Lean's total derivative convention,
--   $$g'(t)=R^{-1}f'\!\left(\frac{t-c}{R}\right),$$
--   and
--   $$g''(t)=(R^{-1})^2f''\!\left(\frac{t-c}{R}\right).$$
--
--   No differentiability assumptions and no condition $R\ne0$ are required in the formal statement.
--
--   This is a generic scalar calculus identity used in rescaling cutoff profiles.
--
--   **Formalization Note** The derivatives are Lean's total `deriv` operators, so the statement includes degenerate cases such as $R=0$.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean#L380-L417 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.Profile`, declaration `FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv_408915f (f : ℝ → ℝ) (c R t : ℝ) :
    deriv (fun s => f ((s - c) / R)) t = R⁻¹ * deriv f ((t - c) / R) ∧
      deriv (deriv (fun s => f ((s - c) / R))) t = (R⁻¹) ^ 2 * deriv (deriv f) ((t - c) / R) := by sorry
