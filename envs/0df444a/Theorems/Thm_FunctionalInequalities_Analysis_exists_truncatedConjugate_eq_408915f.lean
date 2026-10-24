-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_408915f
-- name    : FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:14.705845+00:00
-- url     : https://prove2.me/theorems/e234e3f3-f408-4b3e-8954-bb0e06badf05
-- title:
--   Attainment of the Truncated Conjugate
-- statement:
--   This states attainment and domination for a truncated conjugate.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be continuous, let $M\ge0$, and let $p\in E$. The supremum over the closed ball $\overline B(0,M)$ is attained: there exists $x\in\overline B(0,M)$ such that
--
--   $$
--   \operatorname{truncatedConjugate}(u,M,p)=\langle p,x\rangle-u(x).
--   $$
--
--   Moreover, every point of the ball gives a value no larger than the truncated conjugate:
--
--   $$
--   \forall y\in\overline B(0,M),\qquad \langle p,y\rangle-u(y)\le\operatorname{truncatedConjugate}(u,M,p).
--   $$
--
--   The declaration is `exists_truncatedConjugate_eq`. It is a compactness result and does not assert attainment of the unrestricted Legendre transform.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1291-L1306 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.exists_truncatedConjugate_eq`; the repository is private at upload time).

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
section LT11F2TruncatedConjugate
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
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_408915f {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (p : E) :
    (∃ x ∈ closedBall (0 : E) M, truncatedConjugate u M p = ⟪p, x⟫ - u x) ∧
      ∀ x ∈ closedBall (0 : E) M, ⟪p, x⟫ - u x ≤ truncatedConjugate u M p := by sorry
