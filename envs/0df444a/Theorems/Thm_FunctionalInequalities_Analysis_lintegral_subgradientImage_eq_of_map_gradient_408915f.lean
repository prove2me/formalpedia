-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lintegral_subgradientImage_eq_of_map_gradient_408915f
-- name    : FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:00.147756+00:00
-- url     : https://prove2.me/theorems/b9924439-d11a-43b4-98a4-da700abaf9ba
-- title:
--   Subgradient Image Integral Identity
-- statement:
--   This is the Alexandrov identity in push-forward form.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex. Let $\nu,\mu$ be measures such that:
--
--   1. $\nu\ll\operatorname{vol}$.
--   2. The push-forward of $\nu$ by `gradient` equals $\mu$:
--      $$\nu\mathbin{\#}\nabla u=\mu.$$
--   3. $\mu\ll\operatorname{vol}$.
--   4. $S\subseteq E$ is compact.
--   5. $g:E\to[0,\infty]$ is measurable.
--
--   Then, with `subgradientImage` denoting $\partial u(S)$,
--   $$\int_{\partial u(S)} g(p)\,d\mu(p)=\int_S g(\nabla u(x))\,d\nu(x).$$
--
--   The identity is a reusable change-of-variables formula; both sides are `ENNReal` lower integrals.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L74-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
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

theorem FunctionalInequalities.Analysis.lintegral_subgradientImage_eq_of_map_gradient_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {ν μ : Measure E} (hν : ν ≪ (volume : Measure E)) (hmap : ν.map (gradient u) = μ)
    (hac : μ ≪ (volume : Measure E))
    {S : Set E} (hS : IsCompact S) (g : E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in subgradientImage u S, g p ∂μ = ∫⁻ x in S, g (gradient u x) ∂ν := by sorry
