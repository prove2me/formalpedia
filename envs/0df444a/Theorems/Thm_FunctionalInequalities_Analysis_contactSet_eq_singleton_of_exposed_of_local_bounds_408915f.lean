-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contactSet_eq_singleton_of_exposed_of_local_bounds_408915f
-- name    : FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:49.203288+00:00
-- url     : https://prove2.me/theorems/a720caa3-baca-4ded-85c2-01f55d4979ef
-- title:
--   Localized Exposed Contact Set Is Singleton
-- statement:
--   This is the localized Caffarelli contact-set lemma.
--
--   Let $E$ be a nontrivial finite-dimensional real inner-product space with its Borel measurable structure, and let $u:E\to\mathbb R$ be convex. For $x_0,p\in E$, assume the affine function $u(x_0)+\langle p,x-x_0\rangle$ supports $u$ from below:
--   $$u(x_0)+\langle p,y-x_0\rangle\le u(y)\quad\text{for all }y\in E.$$
--   Let
--   $$C=\{x:u(x)=u(x_0)+\langle p,x-x_0\rangle\}.$$
--   Assume:
--
--   1. $C$ is compact.
--   2. $z\in C$ and $\|\theta\|=1$.
--   3. Every other contact point is strictly exposed from $z$ in direction $\theta$: if $x\in C$ and $x\ne z$, then $\langle x-z,\theta\rangle<0$.
--   4. $h>0$.
--   5. There is an open set $U$ containing the slab piece $C\cap\{x:-h\le\langle x-z,\theta\rangle\}$.
--   6. For every compact $Q\subseteq U$, there are real numbers $a,b$ with $a>0$ such that every open $G$ with $\overline G\subseteq Q$ satisfies
--      $$\operatorname{ofReal}(a)\,\operatorname{vol}(G)\le\operatorname{vol}(\partial u(G))\le\operatorname{ofReal}(b)\,\operatorname{vol}(G),$$
--      where the measures are `ENNReal` values and `subgradientImage` is written as $\partial u(G)$.
--
--   Then
--   $$C=\{z\}.$$
--
--   This is a localized technical form of the exposed-contact argument and is reusable when Alexandrov bounds are available only on compact subsets of an open region.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L670-L1011 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds`; the repository is private at upload time).

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
section LT11E7LocalizedContactLemma
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
variable [FiniteDimensional ℝ E]
section MeasurableSpace
variable [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 4000000

theorem FunctionalInequalities.Analysis.contactSet_eq_singleton_of_exposed_of_local_bounds_408915f {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) (hC : IsCompact {x | u x = u x₀ + ⟪p, x - x₀⟫})
    {z θ : E} (hz : u z = u x₀ + ⟪p, z - x₀⟫) (hθ : ‖θ‖ = 1)
    (hexp : ∀ x, u x = u x₀ + ⟪p, x - x₀⟫ → x ≠ z → ⟪x - z, θ⟫ < 0) {h : ℝ} (hh : 0 < h)
    {U : Set E} (hU : IsOpen U)
    (hCU : {x | u x = u x₀ + ⟪p, x - x₀⟫} ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U)
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ U → ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G →
      closure G ⊆ Q →
      ENNReal.ofReal a * (volume : Measure E) G ≤ (volume : Measure E) (subgradientImage u G) ∧
      (volume : Measure E) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure E) G) :
    {x | u x = u x₀ + ⟪p, x - x₀⟫} = {z} := by sorry
