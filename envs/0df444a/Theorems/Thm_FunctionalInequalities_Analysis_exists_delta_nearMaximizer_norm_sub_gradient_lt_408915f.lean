-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_delta_nearMaximizer_norm_sub_gradient_lt_408915f
-- name    : FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:35.290244+00:00
-- url     : https://prove2.me/theorems/25bc8157-5576-409b-a0eb-6a58c6710aa3
-- title:
--   Near-Maximizers Concentrate Near the Legendre Gradient
-- statement:
--   This is a pointwise stability statement for Legendre maximizers.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, let $\phi:E\to\overline{\mathbb R}$ be a `ProperPotential`, and let $y$ lie in the interior of the finite domain of `legendre φ`. Assume that
--   $$q\mapsto(\operatorname{legendre}(\phi)(q))_{\mathrm{toReal}}$$
--   is differentiable at $y$. Then for every $\varepsilon>0$ there exists $\delta>0$ such that every $z\in E$ satisfying
--   $$\bigl((\operatorname{legendre}(\phi)(y))_{\mathrm{toReal}}-\delta\bigr)
--   \le \langle z,y\rangle-\phi(z)$$
--   obeys
--   $$\left\|z-\nabla\bigl((\operatorname{legendre}(\phi))_{\mathrm{toReal}}\bigr)(y)\right\|<\varepsilon.$$
--
--   The near-maximality condition is quantified directly over $z$; no maximizing sequence or selected maximizer is assumed. This is the concentration estimate used in first-variation arguments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean#L33-L232 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Derivative`, declaration `FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Calculus.FDeriv.Basic
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
section NearMaximizer
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

theorem FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt_408915f
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : y ∈ interior {q : E | legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q : E => (legendre φ q).toReal) y) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ z : E,
      (((legendre φ y).toReal - δ : ℝ) : EReal) ≤
          (inner ℝ z y : EReal) - φ z →
        ‖z - gradient (fun q : E => (legendre φ q).toReal) y‖ < ε := by sorry
