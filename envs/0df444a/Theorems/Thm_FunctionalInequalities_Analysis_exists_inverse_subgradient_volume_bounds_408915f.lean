-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_inverse_subgradient_volume_bounds_408915f
-- name    : FunctionalInequalities.Analysis.exists_inverse_subgradient_volume_bounds_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:15.41988+00:00
-- url     : https://prove2.me/theorems/9190f60a-fc1f-459d-95ef-9e67c8338e83
-- title:
--   Inverse Subgradient Volume Bounds
-- statement:
--   This establishes reciprocal Alexandrov volume bounds.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure. Let $u:E\to\mathbb R$ be Lipschitz and convex, and assume
--   $$\int_E e^{-u(x)}\,d\operatorname{vol}(x)=1.$$
--   Let $\mu$ be a measure satisfying
--   $$((\operatorname{vol})\text{ tilted by }-u)\mathbin{\#}\nabla u=\mu,$$
--   where `gradient` is the Lean gradient map. Let $\rho:E\to[0,\infty]$ be measurable and satisfy $\mu=\rho\,\operatorname{vol}$ via `withDensity`. Let $K\subseteq E$ be closed and convex. Suppose $c,C\in\mathbb R$ with $c>0$ and, for every $p\in K$,
--   $$\operatorname{ofReal}(c)\le\rho(p)\le\operatorname{ofReal}(C).$$
--   For every $M\in\mathbb R$, there exist $a,b\in\mathbb R$ with $a>0$ such that every open $G\subseteq K$ whose inverse subgradient image is contained in $\overline B(0,M)$ satisfies
--   $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le \operatorname{vol}\bigl(\{x:\exists p\in G,\ p\in\partial u(x)\}\bigr)\le \operatorname{ofReal}(b)\,\operatorname{vol}(G).$$
--
--   The conclusion provides the local two-sided bounds needed in the Caffarelli argument. All measure inequalities are in `ENNReal`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2454-L2606 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.exists_inverse_subgradient_volume_bounds`; the repository is private at upload time).

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
section LT11F4ReciprocalAlexandrovBounds
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
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.exists_inverse_subgradient_volume_bounds_408915f
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure E) = 1)
    {μ : Measure E} (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) = μ)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (hμ : μ = (volume : Measure E).withDensity ρ)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    {c C : ℝ} (hc : 0 < c) (hρK : ∀ p ∈ K, ENNReal.ofReal c ≤ ρ p ∧ ρ p ≤ ENNReal.ofReal C)
    (M : ℝ) :
    ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → G ⊆ K →
      {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ⊆ closedBall (0 : E) M →
      ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ∧
        (volume : Measure E) {x | ∃ p ∈ G, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} ≤
          ENNReal.ofReal b * (volume : Measure E) G := by sorry
