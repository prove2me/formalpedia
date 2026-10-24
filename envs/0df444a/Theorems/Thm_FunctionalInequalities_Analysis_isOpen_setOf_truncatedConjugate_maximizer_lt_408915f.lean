-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_isOpen_setOf_truncatedConjugate_maximizer_lt_408915f
-- name    : FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:57.797717+00:00
-- url     : https://prove2.me/theorems/50ad6822-9198-49bb-bebd-975f45a579aa
-- title:
--   Open Slopes With Interior Truncated Maximizers
-- statement:
--   This proves openness of a set of admissible slopes for the truncated conjugate.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous, and let $M\in\mathbb R$ satisfy $0\le M$. Define the set of slopes $p$ such that every maximizer $x$ in the closed ball $\overline B(0,M)$ of `truncatedConjugate` satisfies $\|x\|<M$:
--   $$\left\{p:\forall x\in\overline B(0,M),\quad u_M^*(p)=\langle p,x\rangle-u(x)\Rightarrow\|x\|<M\right\}.$$
--   This set is open.
--
--   The result is a technical topological ingredient for identifying subgradient images of the truncated conjugate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1551-L1574 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.isOpen_setOf_truncatedConjugate_maximizer_lt_408915f {u : E → ℝ} (hu : Continuous u) {M : ℝ}
    (hM : 0 ≤ M) :
    IsOpen {p : E | ∀ x ∈ closedBall (0 : E) M,
      truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M} := by sorry
