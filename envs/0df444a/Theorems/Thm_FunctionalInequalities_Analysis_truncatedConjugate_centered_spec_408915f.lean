-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_truncatedConjugate_centered_spec_408915f
-- name    : FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:10.242529+00:00
-- url     : https://prove2.me/theorems/4ec349b4-1f6d-40d1-aeca-35a2fb0322ca
-- title:
--   Centered Truncated Conjugate Properties
-- statement:
--   This describes the centered truncated conjugate around an interior point.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$ be convex, let $M\in\mathbb R$, and let $x_c\in E$ satisfy $\|x_c\|<M$. Define
--   $$f(p)=u_M^*(p)-\langle p,x_c\rangle+u(x_c).$$
--   Then:
--
--   1. $f(p)\ge0$ for every $p$.
--   2. $f(p)=0$ exactly when $p$ is a subgradient of $u$ at $x_c$:
--      $$f(p)=0\iff\forall y,\ u(x_c)+\langle p,y-x_c\rangle\le u(y).$$
--   3. Every sublevel set $\{p:f(p)\le R\}$ is compact for every $R\in\mathbb R$.
--
--   This provides the compact sublevel structure needed for the contact-set uniqueness argument.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean#L1329-L1426 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Caffarelli`, declaration `FunctionalInequalities.Analysis.truncatedConjugate_centered_spec`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.truncatedConjugate_centered_spec_408915f {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {M : ℝ} {xc : E}
    (hxc : ‖xc‖ < M) :
    (∀ p, 0 ≤ truncatedConjugate u M p - ⟪p, xc⟫ + u xc) ∧
    (∀ p, truncatedConjugate u M p - ⟪p, xc⟫ + u xc = 0 ↔ ∀ y, u xc + ⟪p, y - xc⟫ ≤ u y) ∧
    ∀ R : ℝ, IsCompact {p | truncatedConjugate u M p - ⟪p, xc⟫ + u xc ≤ R} := by sorry
