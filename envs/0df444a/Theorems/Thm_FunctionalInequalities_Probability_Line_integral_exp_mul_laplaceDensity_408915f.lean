-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_Line_integral_exp_mul_laplaceDensity_408915f
-- name    : FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:31.944994+00:00
-- url     : https://prove2.me/theorems/84627e86-f1c7-4c55-9165-1b1b299ee2d3
-- title:
--   Exponential Integral Against the Laplace Density
-- statement:
--   This lemma evaluates the exponentially weighted Laplace density on its stated local parameter range.
--
--   Let $\beta,w\in\mathbb R$ satisfy $\beta>0$ and $|w|<\beta$. Define $\rho_\beta(s)=(\beta/2)e^{-\beta|s|}$, the function `laplaceDensity` $\beta$. With Lebesgue measure $ds$ on $\mathbb R$,
--   $$
--   s\mapsto e^{ws}\rho_\beta(s)\in L^1(ds),\qquad
--   \int_{\mathbb R}e^{ws}\rho_\beta(s)\,ds=\frac{\beta^2}{\beta^2-w^2}.
--   $$
--
--   The statement supplies the density-level integrability and integral needed for the Laplace moment generating function. It makes no assertion for $|w|\ge\beta$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L104-L234 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Line.Laplace`, declaration `FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_Laplace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.MGFAnalytic

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Line
end FunctionalInequalities.Probability.Line
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Line
section Moments
open ProbabilityTheory Filter Set
open scoped Topology

theorem FunctionalInequalities.Probability.Line.integral_exp_mul_laplaceDensity_408915f {β w : ℝ} (hβ : 0 < β) (hw : |w| < β) :
    MeasureTheory.Integrable (fun s => Real.exp (w * s) * laplaceDensity β s) ∧
      ∫ s, Real.exp (w * s) * laplaceDensity β s = β ^ 2 / (β ^ 2 - w ^ 2) := by sorry
