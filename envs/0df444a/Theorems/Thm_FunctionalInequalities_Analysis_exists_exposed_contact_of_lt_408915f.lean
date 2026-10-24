-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_exposed_contact_of_lt_408915f
-- name    : FunctionalInequalities.Analysis.exists_exposed_contact_of_lt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:17.843852+00:00
-- url     : https://prove2.me/theorems/3b27385b-0748-4e0e-acaf-04aedd59346e
-- title:
--   Strictly Exposed Contact Below a Level
-- statement:
--   This establishes the existence of a strictly exposed contact point below a prescribed level.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $u:E\to\mathbb R$ be convex. Let $x,p\in E$ satisfy
--   $$u(x)+\langle p,y-x\rangle\le u(y)\quad\text{for all }y\in E.$$
--   For $R\in\mathbb R$, assume $u(x)<R$ and that the sublevel set $\{y:u(y)\le R\}$ is compact. Then there exist $z,\theta\in E$ such that
--   $$u(z)=u(x)+\langle p,z-x\rangle,\qquad u(z)<R,$$
--   and every other contact point in the sublevel set is strictly separated:
--   $$u(y)=u(x)+\langle p,y-x\rangle\ \land\ u(y)\le R\ \land\ y\ne z
--   \ \Longrightarrow\ \langle y-z,\theta\rangle<0.$$
--
--   The result supplies an exposed point for later contact-set arguments; it does not assert uniqueness of all contacts without the additional local volume hypotheses.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1202-L1260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.exists_exposed_contact_of_lt`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.exists_exposed_contact_of_lt_408915f {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) {R : ℝ} (hR : u x < R) (hK : IsCompact {y | u y ≤ R}) :
    ∃ z θ : E, u z = u x + ⟪p, z - x⟫ ∧ u z < R ∧
      ∀ y, u y = u x + ⟪p, y - x⟫ → u y ≤ R → y ≠ z → ⟪y - z, θ⟫ < 0 := by sorry
