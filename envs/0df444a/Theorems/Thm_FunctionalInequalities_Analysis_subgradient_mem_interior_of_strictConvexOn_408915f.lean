-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradient_mem_interior_of_strictConvexOn_408915f
-- name    : FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:12.59091+00:00
-- url     : https://prove2.me/theorems/83f22eeb-c0ad-45c3-a34d-d5a548ec1db4
-- title:
--   Strictly Convex Subgradients Lie In Interior
-- statement:
--   This proves interior membership for subgradients of a strictly convex function.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be strictly convex. Let $K\subseteq E$ be convex with nonempty interior. Assume every subgradient of $u$ belongs to $K$:
--   $$\forall x,p,\quad \bigl[\forall y,\ u(x)+\langle p,y-x\rangle\le u(y)\bigr]\Rightarrow p\in K.$$
--   Then every such subgradient lies in the interior:
--   $$\forall x,p,\quad \bigl[\forall y,\ u(x)+\langle p,y-x\rangle\le u(y)\bigr]\Rightarrow p\in\operatorname{int}K.$$
--
--   This strengthens closed-range containment and is used when deriving local density bounds.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1159-L1200 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn`; the repository is private at upload time).

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
section LT11F1StrictConvexityElementary
open Set
open scoped RealInnerProductSpace
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

theorem FunctionalInequalities.Analysis.subgradient_mem_interior_of_strictConvexOn_408915f {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {K : Set E} (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty)
    (hK : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) → p ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ interior K := by sorry
