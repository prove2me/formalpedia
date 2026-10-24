-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inner_hasFDerivAt_resolvent_symm_408915f
-- name    : FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:13.195734+00:00
-- url     : https://prove2.me/theorems/7dd5a69c-2c0b-4503-96bf-d26d3308113e
-- title:
--   Symmetry and Firm Nonexpansiveness of the Resolvent Derivative
-- statement:
--   This statement records structural properties of a differentiable resolvent.
--
--   Let $E$ be a real inner-product space, let $f:E\to\mathbb R$ and $P:E\to E$, and assume
--
--   $$f(Pz)+\langle z-Pz,y-Pz\rangle\le f(y)\qquad(z,y\in E).$$
--
--   Fix $z\in E$ and suppose that $P$ has Fréchet derivative $T:E\to E$ at $z$. Then, for every $v,w\in E$,
--
--   $$\langle Tv,w\rangle=\langle v,Tw\rangle,
--   \qquad \|Tv\|^2\le \langle Tv,v\rangle.$$
--
--   The declaration `inner_hasFDerivAt_resolvent_symm` provides symmetry and the firmly nonexpansive quadratic inequality for the derivative at a single point. It is a local linear-algebraic property and does not assert global differentiability of $P$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean#L241-L288 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Proximal`, declaration `FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.inner_hasFDerivAt_resolvent_symm_408915f
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E}
    {T : E →L[ℝ] E} (hT : HasFDerivAt P T z) (v w : E) :
    ⟪T v, w⟫ = ⟪v, T w⟫ ∧ ‖T v‖ ^ 2 ≤ ⟪T v, v⟫ := by sorry
