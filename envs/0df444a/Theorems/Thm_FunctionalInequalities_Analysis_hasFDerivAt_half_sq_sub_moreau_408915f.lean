-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasFDerivAt_half_sq_sub_moreau_408915f
-- name    : FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:14.1438+00:00
-- url     : https://prove2.me/theorems/4254c6f9-93b6-4f2d-95ec-75e423d29af1
-- title:
--   Derivative of the Quadratic Minus Moreau Expression
-- statement:
--   This is an auxiliary differentiability statement for a resolvent-type map.
--
--   Let $E$ be a real inner-product space, let $f:E\to\mathbb R$ and $P:E\to E$, and assume that for all $z,y\in E$,
--
--   $$f(Pz)+\langle z-Pz,y-Pz\rangle\le f(y).$$
--
--   Then, at every $z\in E$, the function
--
--   $$w\longmapsto \frac12\|w\|^2-\left(f(Pw)+\frac12\|Pw-w\|^2\right)$$
--
--   has Fréchet derivative represented by the inner product with $Pz$:
--
--   $$D\!\left[\frac12\|\cdot\|^2-f(P\cdot)-\frac12\|P\cdot-\cdot\|^2\right]_z(v)=\langle Pz,v\rangle.$$
--
--   In Lean this derivative is expressed as `HasFDerivAt` with linear map `innerSL ℝ (P z)`. The result requires no convexity hypothesis beyond the displayed subgradient inequality.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L202-L239 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, declaration `FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
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
section LT12D3MoreauSymmetricDerivative
open Set Filter
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

theorem FunctionalInequalities.Analysis.hasFDerivAt_half_sq_sub_moreau_408915f
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
    HasFDerivAt (fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2))
      (innerSL ℝ (P z)) z := by sorry
