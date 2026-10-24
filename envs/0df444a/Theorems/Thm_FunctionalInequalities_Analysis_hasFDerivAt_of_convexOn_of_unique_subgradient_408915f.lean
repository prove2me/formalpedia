-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_of_convexOn_of_unique_subgradient_408915f
-- name    : FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:34.373222+00:00
-- url     : https://prove2.me/theorems/51ea5670-a5a1-4206-a27e-b6bbd339fa24
-- title:
--   Differentiability From Unique Convex Subgradient
-- statement:
--   This is an auxiliary differentiability criterion for convex functions.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex. Fix $x,g\in E$. Assume $g$ is a subgradient at $x$:
--   $$u(x)+\langle g,y-x\rangle\le u(y)\quad\text{for all }y,$$
--   and assume it is unique: every $q$ satisfying the same supporting inequality equals $g$. Then $u$ has a Fréchet derivative at $x$, represented through the inner product by $g$:
--   $$\operatorname{HasFDerivAt}(u,\operatorname{toDual}(g),x).$$
--
--   The result is used to pass from pointwise uniqueness of subgradients to continuous differentiability.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L656-L833 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `_private.FunctionalInequalities.Analysis.Convex.Subgradient.0.FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient`; the repository is private at upload time).

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
section LT5CUniqueSubgradientDifferentiable
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

lemma FunctionalInequalities.Analysis.hasFDerivAt_of_convexOn_of_unique_subgradient_408915f {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (x g : E)
    (hg : ∀ y, u x + ⟪g, y - x⟫ ≤ u y)
    (huniq : ∀ q, (∀ y, u x + ⟪q, y - x⟫ ≤ u y) → q = g) :
    HasFDerivAt u ((InnerProductSpace.toDual ℝ E) g) x := by sorry
