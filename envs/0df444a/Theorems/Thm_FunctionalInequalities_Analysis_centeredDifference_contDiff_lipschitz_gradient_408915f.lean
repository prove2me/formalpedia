-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_centeredDifference_contDiff_lipschitz_gradient_408915f
-- name    : FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:50.129417+00:00
-- url     : https://prove2.me/theorems/29eae663-8b4b-4a47-b981-bae0a442d59f
-- title:
--   Regularity of a Centered Second Difference
-- statement:
--   This formalizes the regularity estimate for a centered second difference, cited in the literature register as part of Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $u:\mathbb R^n\to\mathbb R$ be $C^1$, let $G\in[0,\infty)$, and suppose its gradient is $G$-Lipschitz. For any $h\in\mathbb R^n$, define
--
--   $$
--   v_h(x)=u(x+h)+u(x-h)-2u(x).
--   $$
--
--   Then $v_h$ is $C^1$ and its gradient is $4G$-Lipschitz:
--
--   $$
--   \operatorname{Lip}(\nabla v_h)\le 4G.
--   $$
--
--   The Lean declaration is `centeredDifference_contDiff_lipschitz_gradient`. The result is an adapter for centered-difference estimates and does not assume convexity.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean#L779-L834 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SecondDifference`, declaration `FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.centeredDifference_contDiff_lipschitz_gradient_408915f {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    {G : NNReal} (hG : LipschitzWith G (gradient u))
    (h : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun x => u (x + h) + u (x - h) - 2 * u x) ∧
      LipschitzWith (4 * G)
        (gradient (fun x => u (x + h) + u (x - h) - 2 * u x)) := by sorry
