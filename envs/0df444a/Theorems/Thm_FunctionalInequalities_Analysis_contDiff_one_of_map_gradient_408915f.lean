-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contDiff_one_of_map_gradient_408915f
-- name    : FunctionalInequalities.Analysis.contDiff_one_of_map_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:01.830854+00:00
-- url     : https://prove2.me/theorems/944da474-f44e-490a-9f9f-bbc9fb518307
-- title:
--   Continuous Differentiability of the Moment Potential
-- statement:
--   This formalizes the regularity statement associated with Lemma 2.2 of Klartag, cited in Letwin (arXiv:2607.24164v1), locator Lemma 2.2, with the reviewed relation recorded as partial.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume:
--
--   1. $\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1$.
--   2. $K\subseteq E$ is compact, convex, and has nonempty interior.
--   3. $V:E\to\mathbb R$ is continuous.
--   4. The push-forward of the tilted volume measure by $\nabla u$ equals the measure with density $1_K(p)\operatorname{ofReal}(e^{-V(p)})$.
--
--   Then
--   $$u\in C^1(E),$$
--   formalized as `ContDiff ℝ 1 u`.
--
--   This is the regularity conclusion used for the moment potential in the finite-dimensional compact-target setting.
--
--   **Formalization Note** The statement proves `ContDiff` of order $1$ on the whole finite-dimensional space; it does not state positive-definite Hessian, a global diffeomorphism, or a pointwise Monge–Ampère equation.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.2 (Klartag [41]). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L2151-L2313 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.contDiff_one_of_map_gradient`; the repository is private at upload time).

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
section LT11F7MomentC1
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
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.contDiff_one_of_map_gradient_408915f
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    {V : E → ℝ} (hV : Continuous V)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p)))) :
    ContDiff ℝ 1 u := by sorry
