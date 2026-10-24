-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_strictConvexOn_of_map_gradient_408915f
-- name    : FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:00.895802+00:00
-- url     : https://prove2.me/theorems/158eaa0b-ace4-4d81-805a-c72da3d54c67
-- title:
--   Strict Convexity From Compact Target Push-Forward
-- statement:
--   This states strict convexity of a moment potential under a compact-target push-forward hypothesis.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume
--   $$\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1.$$
--   Let $K\subseteq E$ be compact, convex, and nonempty. Let $V:E\to\mathbb R$ be continuous. Assume that the push-forward of the tilted volume measure by $\nabla u$ equals the volume measure with density $1_K(p)\operatorname{ofReal}(e^{-V(p)})$. Then
--   $$u\text{ is strictly convex on }E.$$
--
--   The result packages the contact-set argument into a global strict-convexity conclusion. It does not assert differentiability.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1984-L2087 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Caffarelli
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Normalization
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F6MomentStrictConvexity
open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.strictConvexOn_of_map_gradient_408915f {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    StrictConvexOn ℝ univ u := by sorry
