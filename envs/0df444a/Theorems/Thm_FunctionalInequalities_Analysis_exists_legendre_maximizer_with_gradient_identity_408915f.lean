-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_legendre_maximizer_with_gradient_identity_408915f
-- name    : FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:57.979734+00:00
-- url     : https://prove2.me/theorems/af770495-b1fd-46fe-a826-010a08029e15
-- title:
--   Legendre Maximizer and Dual Gradient
-- statement:
--   This is an attainment statement for the Legendre transform.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential` and lower semicontinuous, and let $y$ belong to the interior of $\{q:\phi^*(q)\ne+\infty\}$. Then there exists $z\in E$ such that
--
--   $$\langle z,y\rangle-\phi(z)=\phi^*(y).$$
--
--   Moreover, if $q\mapsto(\phi^*(q))_{\mathrm{toReal}}$ is differentiable at $y$, then
--   $$z=\nabla\big((\phi^*)_{\mathrm{toReal}}\big)(y).$$
--
--   Thus every interior point of the finite Legendre domain has a primal maximizer, with the stated gradient identification under the additional differentiability implication.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L334-L370 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section Attainment
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_408915f
    (φ : E → EReal) (hφ : ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤}) :
    ∃ z : E,
      (inner ℝ z y : EReal) - φ z = legendre φ y ∧
      (DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y →
        z = gradient (fun q : E => (legendre φ q).toReal) y) := by sorry
