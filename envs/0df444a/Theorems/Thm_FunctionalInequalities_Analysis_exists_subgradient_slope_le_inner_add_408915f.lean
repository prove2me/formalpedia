-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_408915f
-- name    : FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:01.96803+00:00
-- url     : https://prove2.me/theorems/68753be5-0d3f-42ca-b1ca-97903006ebd3
-- title:
--   Subgradient Realizing the One-Sided Convex Slope
-- statement:
--   This is an auxiliary max-formula statement for directional slopes of finite convex functions.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex on all of $E$. For every $x,v\in E$, there exists $g\in E$ such that:
--
--   1. $g$ is a subgradient of $u$ at $x$:
--      $$u(x)+\langle g,y-x\rangle\le u(y)\qquad\text{for every }y\in E.$$
--   2. For every $\varepsilon>0$, there exists $t>0$ with
--      $$\frac{u(x+t v)-u(x)}{t}\le \langle g,v\rangle+\varepsilon.$$
--
--   Thus the pairing with $v$ is approximated from above by positive directional difference quotients, while the subgradient inequality supplies the corresponding lower bound. The declaration `exists_subgradient_slope_le_inner_add` is useful for selecting subgradients compatible with one-sided directional derivatives.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L202-L553 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
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
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LT5ASubgradientMaxFormula
open scoped RealInnerProductSpace

theorem FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x v : E) :
    ∃ g : E, (∀ y, u x + ⟪g, y - x⟫ ≤ u y) ∧
      ∀ ε > 0, ∃ t > 0, (u (x + t • v) - u x) / t ≤ ⟪g, v⟫ + ε := by sorry
