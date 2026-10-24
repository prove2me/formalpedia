-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_contDiff_one_of_convexOn_of_differentiable_408915f
-- name    : FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:20.787452+00:00
-- url     : https://prove2.me/theorems/7a9fed03-f08c-47c4-8c9c-1a7031a5ad09
-- title:
--   Differentiable Convex Functions Are C¹
-- statement:
--   This proves the finite-dimensional regularity fact that a differentiable convex function is $C^1$.
--
--   Let $E$ be a finite-dimensional real normed space and let $u:E\to\mathbb R$. If $u$ is convex on all of $E$ and differentiable everywhere, then
--
--   $$
--   u\in C^1(E),\qquad\text{that is,}\qquad \operatorname{ContDiff}_{\mathbb R}^{1}(u).
--   $$
--
--   The declaration is `contDiff_one_of_convexOn_of_differentiable`. No quantitative Lipschitz estimate for the derivative is included, and finite dimensionality is essential to the stated result.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L30-L111 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable`; the repository is private at upload time).

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
section ConvexC1

theorem FunctionalInequalities.Analysis.contDiff_one_of_convexOn_of_differentiable_408915f {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) :
    ContDiff ℝ 1 u := by sorry
