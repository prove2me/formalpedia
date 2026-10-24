-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_centeredDifference_nonneg_le_408915f
-- name    : FunctionalInequalities.Analysis.centeredDifference_nonneg_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:25.591528+00:00
-- url     : https://prove2.me/theorems/2cea74d0-2e7c-454d-8663-ca61facb885f
-- title:
--   Nonnegative Convex Centered Difference
-- statement:
--   This formalizes the centered-difference bounds used in the estimate associated with Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u:\mathbb R^n\to\mathbb R$ be convex on the whole space, let $D\in\mathbb R$, and let $h\in\mathbb R^n$. Assume that for every $x$,
--
--   $$
--   u_h(x):=u(x+h)+u(x-h)-2u(x)\le D\|h\|^2.
--   $$
--
--   Then for every $x$,
--
--   $$
--   0\le \nu_h(x)\le D\|h\|^2,
--   $$
--
--   and also $0\le D\|h\|^2$. The declaration is `centeredDifference_nonneg_le`. No differentiability or separate sign assumption on $D$ is made; the nonnegativity follows from convexity and the asserted upper bound.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L837-L871 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.centeredDifference_nonneg_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
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
open scoped RealInnerProductSpace
section CenteredDifference
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.centeredDifference_nonneg_le_408915f {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u)
    {D : ℝ} (h : EuclideanSpace ℝ (Fin n))
    (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    (∀ x, 0 ≤ u (x + h) + u (x - h) - 2 * u x ∧
      u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) ∧
      0 ≤ D * ‖h‖ ^ 2 := by sorry
