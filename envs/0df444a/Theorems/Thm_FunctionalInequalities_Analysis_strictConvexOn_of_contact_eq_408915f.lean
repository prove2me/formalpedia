-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_strictConvexOn_of_contact_eq_408915f
-- name    : FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:28.059465+00:00
-- url     : https://prove2.me/theorems/d6f91dde-b8e5-4a08-844f-88646d10aa50
-- title:
--   Singleton Supporting Contacts Imply Strict Convexity
-- statement:
--   This states that singleton supporting contact sets imply strict convexity.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex. Assume that for every $x,p\in E$, whenever
--   $$u(x)+\langle p,y-x\rangle\le u(y)\quad\text{for all }y,$$
--   any point $y$ satisfying equality must equal $x:
--   $$u(y)=u(x)+\langle p,y-x\rangle\Longrightarrow y=x.$$
--   Then $u$ is strictly convex on $E$:
--   $$u(a x+b y)<a u(x)+b u(y)$$
--   whenever $x\ne y$, $a,b>0$, and $a+b=1$.
--
--   This is the abstract bridge from uniqueness of supporting contacts to strict convexity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1107-L1157 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.strictConvexOn_of_contact_eq_408915f {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hcontact : ∀ x p : E, (∀ y, u x + ⟪p, y - x⟫ ≤ u y) →
      ∀ y, u y = u x + ⟪p, y - x⟫ → y = x) :
    StrictConvexOn ℝ univ u := by sorry
