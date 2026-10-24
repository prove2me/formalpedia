-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_conjugate_maximizer_eq_gradient_408915f
-- name    : FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:13:26.72815+00:00
-- url     : https://prove2.me/theorems/b97f27cb-412e-47dd-ae70-9435f93222aa
-- title:
--   Conjugate Maximizer Equals Dual Gradient
-- statement:
--   This is the identification part of the dual-differentiability argument from Berman–Berndtsson, arXiv:1207.6128v1, Lemma 2.7 and Appendix 6, and is used for the first-variation framework of Cordero-Erausquin–Klartag, arXiv:1304.0630v1.
--
--   Let $E$ be a finite-dimensional real inner-product space and let $\varphi:E\to[-\infty,\infty]$ be a `ProperPotential`. Let $y$ lie in the interior of the set where the Legendre transform $\varphi^*$ is not $+\infty$, and assume $q\mapsto(\varphi^*(q)).\operatorname{toReal}$ is differentiable at $y$. If $z\in E$ satisfies
--
--   $$
--   \langle z,y\rangle-\varphi(z)=\varphi^*(y),
--   $$
--
--   then
--
--   $$
--   z=\nabla\big((\varphi^*)_{\mathbb R}\big)(y).
--   $$
--
--   The declaration is `conjugate_maximizer_eq_gradient`. The primal potential need not be convex, differentiable, nonnegative, or finite everywhere; existence of a maximizer is not asserted.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean#L37-L196 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.LegendreVariation.Attainment`, declaration `FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient`; the repository is private at upload time).

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
section MaximizerGradient
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set

theorem FunctionalInequalities.Analysis.conjugate_maximizer_eq_gradient_408915f
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    {y : E} (hy : y ∈ interior {q | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ
      (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y) :
    ∀ z : E,
      (inner ℝ z y : EReal) - φ z = FunctionalInequalities.Analysis.legendre φ y →
      z = gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y := by sorry
