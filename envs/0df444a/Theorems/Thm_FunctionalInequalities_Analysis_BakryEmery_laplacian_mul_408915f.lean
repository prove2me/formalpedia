-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_laplacian_mul_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.laplacian_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:28.305572+00:00
-- url     : https://prove2.me/theorems/94576705-28e6-421a-b4e9-04183b3b0d8d
-- title:
--   Product Rule for the Laplacian
-- statement:
--   This theorem is the pointwise product rule for the Euclidean Laplacian.
--
--   Let $E$ be a finite-dimensional complete real inner-product space, let $f,g:E\to\mathbb R$ be twice continuously differentiable, and let $x\in E$. Then
--
--   $$\Delta(fg)(x)=f(x)\Delta g(x)+g(x)\Delta f(x)+2\langle\nabla f(x),\nabla g(x)\rangle.$$
--
--   The identity is a local calculus tool and involves no measure, integrability, or curvature assumptions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean#L593-L620 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Calculus`, declaration `FunctionalInequalities.Analysis.BakryEmery.laplacian_mul`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_mul_408915f {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y => f y * g y) x =
      f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
        2 * ⟪gradient f x, gradient g x⟫ := by sorry
