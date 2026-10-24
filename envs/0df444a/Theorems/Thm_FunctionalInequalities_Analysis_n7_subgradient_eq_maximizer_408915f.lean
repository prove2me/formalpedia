-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_n7_subgradient_eq_maximizer_408915f
-- name    : FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:39.209551+00:00
-- url     : https://prove2.me/theorems/f9aec075-4d44-4ad4-b906-bd4102a26601
-- title:
--   Truncated Conjugate Subgradient Identifies Maximizer
-- statement:
--   This is an auxiliary uniqueness statement for truncated conjugate maximizers.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous and strictly convex, and let $M\ge0$. Let $p,x,g\in E$ satisfy:
--
--   1. $\|x\|<M$.
--   2. $p$ is a subgradient of $u$ at $x$.
--   3. The truncated conjugate satisfies
--      $$u_M^*(p)=\langle p,x\rangle-u(x).$$
--   4. $g$ is a subgradient of the truncated conjugate at $p$:
--      $$u_M^*(p)+\langle g,q-p\rangle\le u_M^*(q)\quad\text{for all }q.$$
--
--   Then
--   $$g=x.$$
--
--   The lemma is used in the identification of the subgradient image of the truncated conjugate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1598-L1655 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `_private.FunctionalInequalities.Analysis.Convex.Caffarelli.0.FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer`; the repository is private at upload time).

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

lemma FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer_408915f {u : E → ℝ}
    (hu : Continuous u) (hstrict : StrictConvexOn ℝ univ u)
    {M : ℝ} (hM : 0 ≤ M) {p x g : E} (hx : ‖x‖ < M)
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x)
    (hg : ∀ q, truncatedConjugate u M p + ⟪g, q - p⟫ ≤ truncatedConjugate u M q) :
    g = x := by sorry
