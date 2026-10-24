-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_lipschitzWith_gradient_of_second_difference_le_408915f
-- name    : FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:30.855691+00:00
-- url     : https://prove2.me/theorems/b89d07ce-d67b-4e04-b2c0-8434fb877ece
-- title:
--   Lipschitz Gradient from a Second-Difference Bound
-- statement:
--   Let $E$ be a complete real inner-product normed space, let $u:E\to\mathbb R$ be convex and differentiable, and let $C\ge0$. If for every $x,h\in E$,
--
--   $$u(x+h)+u(x-h)-2u(x)\le C\|h\|^2,$$
--
--   then the gradient is globally Lipschitz with constant $4C$ (represented in Lean by `Real.toNNReal (4 * C)`):
--
--   $$\|\nabla u(x)-\nabla u(y)\|\le4C\|x-y\|.$$
--
--   This is the standard $C^{1,1}$ consequence of the centered second-difference estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L215-L480 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le`; the repository is private at upload time).

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
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section W0T4SecondDifferenceLipschitz

theorem FunctionalInequalities.Analysis.lipschitzWith_gradient_of_second_difference_le_408915f {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {u : E → ℝ} {C : ℝ}
    (hconv : ConvexOn ℝ Set.univ u) (hdiff : Differentiable ℝ u) (hC : 0 ≤ C)
    (hsd : ∀ x h : E, u (x + h) + u (x - h) - 2 * u x ≤ C * ‖h‖ ^ 2) :
    LipschitzWith (Real.toNNReal (4 * C)) (gradient u) := by sorry
