-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eq_of_contact_of_sublevel_bounds_408915f
-- name    : FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:29.295984+00:00
-- url     : https://prove2.me/theorems/92f675ee-8200-4805-881b-a5b77c6a30ed
-- title:
--   Sublevel Contact Uniqueness
-- statement:
--   This formalizes the Caffarelli contact-set lemma below a level.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, and let $u:E\to\mathbb R$ be convex. Fix $x_0,p\in E$ with
--   $$u(x_0)+\langle p,y-x_0\rangle\le u(y)\quad\text{for all }y\in E.$$
--   Let $R\in\mathbb R$. Assume that $\{y:u(y)\le R\}$ is compact and that every compact $Q\subseteq\{y:u(y)<R\}$ admits constants $a,b\in\mathbb R$ with $a>0$ and the two-sided bounds
--   $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le\operatorname{vol}(\partial u(G))\le\operatorname{ofReal}(b)\,\operatorname{vol}(G)$$
--   for every open $G$ with $\overline G\subseteq Q$. Then every $y$ satisfying $u(y)<R$ and
--   $$u(y)=u(x_0)+\langle p,y-x_0\rangle$$
--   coincides with $x_0$:
--   $$y=x_0.$$
--
--   This is a reusable localized strict-convexity criterion; compactness is required only for the closed sublevel set, not for the full contact set.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1913-L1965 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds`; the repository is private at upload time).

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
section LT11F5SublevelContactLemma
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
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
variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.eq_of_contact_of_sublevel_bounds_408915f {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) {R : ℝ} (hK : IsCompact {y | u y ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {y | u y < R} → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E,
      IsOpen G → closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G)
    {y : E} (hyR : u y < R) (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by sorry
