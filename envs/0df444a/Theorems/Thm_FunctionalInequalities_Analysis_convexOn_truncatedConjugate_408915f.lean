-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convexOn_truncatedConjugate_408915f
-- name    : FunctionalInequalities.Analysis.convexOn_truncatedConjugate_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:59.90171+00:00
-- url     : https://prove2.me/theorems/622c2f5b-6abe-4d13-9a90-41b2a91fc4b3
-- title:
--   Convexity of the Truncated Conjugate
-- statement:
--   This proves convexity of the truncated conjugate.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be continuous. For every $M\ge0$, the function $p\mapsto\operatorname{truncatedConjugate}(u,M,p)$ is convex on all of $E$:
--
--   $$
--   \operatorname{ConvexOn}_{\mathbb R}(E,\operatorname{truncatedConjugate}(u,M)).
--   $$
--
--   The declaration is `convexOn_truncatedConjugate`. The statement concerns the supremum restricted to the closed ball of radius $M$ and makes no claim about strict convexity or differentiability.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1308-L1327 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.convexOn_truncatedConjugate`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.convexOn_truncatedConjugate_408915f {u : E → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) :
    ConvexOn ℝ univ (truncatedConjugate u M) := by sorry
