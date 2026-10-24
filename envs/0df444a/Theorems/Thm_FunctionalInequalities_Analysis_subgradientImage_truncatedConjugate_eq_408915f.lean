-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_truncatedConjugate_eq_408915f
-- name    : FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:01.669993+00:00
-- url     : https://prove2.me/theorems/d3b546c0-99ee-49c7-9b29-d799a36047d5
-- title:
--   Truncated Conjugate Image Identification
-- statement:
--   This gives the Danskin-type identification of a truncated-conjugate subgradient image.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous and strictly convex, and let $M\ge0$. Let $S\subseteq E$ satisfy the interior-maximizer condition: for every $p\in S$ and every $x\in\overline B(0,M)$,
--   $$u_M^*(p)=\langle p,x\rangle-u(x)\Longrightarrow\|x\|<M.$$
--   Then
--   $$\partial(u_M^*)(S)=\left\{x:\exists p\in S,\ \forall y,\ u(x)+\langle p,y-x\rangle\le u(y)\right\}.$$
--
--   This result converts a subgradient image of the truncated conjugate into an inverse subgradient image of $u$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1657-L1687 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq`; the repository is private at upload time).

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
section LT11F3TruncatedConjugateSubgradients
open Set Metric
open scoped RealInnerProductSpace Topology
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

theorem FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq_408915f {u : E → ℝ} (hu : Continuous u)
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M) {S : Set E}
    (hS : ∀ p ∈ S, ∀ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M) :
    subgradientImage (truncatedConjugate u M) S = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by sorry
