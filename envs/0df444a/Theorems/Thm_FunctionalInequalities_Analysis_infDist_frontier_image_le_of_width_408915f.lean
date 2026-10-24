-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_infDist_frontier_image_le_of_width_408915f
-- name    : FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:48.163408+00:00
-- url     : https://prove2.me/theorems/8900d15e-c862-4b8b-b6db-ad0b8f308a2e
-- title:
--   Affine Image Frontier Bound from Widths
-- statement:
--   This formalizes the affine-normalized frontier-distance estimate used in the Caffarelli argument.
--
--   Let $E$ be finite-dimensional, let $S\subseteq E$ be open and bounded, let $x\in S$, and let $\theta$ be a unit vector. Suppose $\alpha\ge0$, $\beta>0$, and
--
--   $$
--   \langle y-x,\theta\rangle\le\alpha\quad(y\in S),
--   $$
--
--   while some $y\in S$ satisfies $\langle y-x,\theta\rangle\le-\beta$. If $e:E\simeq_A E$ is an affine equivalence with $e(S)\subseteq\overline B(0,C_0)$ for $C_0>0$, then
--
--   $$
--   \operatorname{infDist}(e(x),\partial(e(S)))\le\frac{2C_0\alpha}{\beta}.
--   $$
--
--   The declaration is `infDist_frontier_image_le_of_width`. The inequalities are respectively non-strict above and strict in the positivity hypothesis for $\beta$ and $C_0$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L25-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width`; the repository is private at upload time).

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
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.infDist_frontier_image_le_of_width_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {S : Set E} (hS : IsOpen S)
    (hb : Bornology.IsBounded S) {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hup : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ α) (hlow : ∃ y ∈ S, ⟪y - x, θ⟫ ≤ -β)
    (e : E ≃ᵃ[ℝ] E) {C₀ : ℝ} (hC₀ : 0 < C₀) (himg : e '' S ⊆ closedBall (0 : E) C₀) :
    infDist (e x) (frontier (e '' S)) ≤ 2 * C₀ * α / β := by sorry
