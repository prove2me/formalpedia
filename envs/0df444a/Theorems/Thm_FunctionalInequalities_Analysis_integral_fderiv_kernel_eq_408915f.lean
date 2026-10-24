-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_fderiv_kernel_eq_408915f
-- name    : FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:48.822834+00:00
-- url     : https://prove2.me/theorems/c2b34d84-8fef-4e93-a631-fd0316bcd9cf
-- title:
--   Derivative Kernel Integration Identity
-- statement:
--   This private technical lemma gives an integration-by-parts identity for a Lipschitz change of variables.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its Borel measure. Let $F:E\to E$ be Lipschitz with constant bounded by $G\in[0,\infty)$, let $k:E\to\mathbb R$ be $C^1$ with compact support, let $x,v\in E$, and let $\ell:E\to\mathbb R$ be continuous linear. Then
--
--   $$
--   \int \mathrm Dk(t)[v]\,\ell(F(x-t))\,dt
--   =
--   \int k(t)\,\ell\!\left(DF(x-t)[v]\right)\,dt.
--   $$
--
--   The derivative $DF$ is `fderiv ℝ F` and is used pointwise in the displayed expression. The result is used to establish derivative formulas for mollified Lipschitz maps.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean#L456-L510 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Basic`, declaration `_private.FunctionalInequalities.Analysis.Mollification.Basic.0.FunctionalInequalities.Analysis.integral_fderiv_kernel_eq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LipschitzConvolution
open MeasureTheory
open scoped Convolution
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Analysis.integral_fderiv_kernel_eq_408915f
    {F : E → E} {G : NNReal} (hF : LipschitzWith G F)
    (k : E → ℝ) (hk : ContDiff ℝ 1 k) (hc : HasCompactSupport k)
    (x v : E) (ℓ : E →L[ℝ] ℝ) :
    (∫ t, fderiv ℝ k t v * ℓ (F (x - t))) =
      ∫ t, k t * ℓ (fderiv ℝ F (x - t) v) := by sorry
