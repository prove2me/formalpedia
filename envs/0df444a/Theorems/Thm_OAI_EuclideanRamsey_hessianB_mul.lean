-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_hessianB_mul
-- name    : OAI.EuclideanRamsey.hessianB_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:00:22.483998+00:00
-- url     : https://prove2.me/theorems/49b4be51-e36d-4715-8af9-e14010e96bb7
-- title:
--   Product rule for the second derivative of real-valued functions
-- statement:
--   Let $E$ be a real normed space and $f,g:E\to\mathbb{R}$ infinitely differentiable functions. Write $Df(x)[v]$ for the Fréchet derivative of $f$ at $x$ in direction $v$, and $D^2f(x)[v,w]=\bigl(D(Df)(x)[v]\bigr)[w]$ for the second derivative, the derivative of $y\mapsto Df(y)$ at $x$ regarded as a bilinear form. Then for all $x,v,w\in E$
--   $$D^2(fg)(x)[v,w]=f(x)\,D^2g(x)[v,w]+g(x)\,D^2f(x)[v,w]+Df(x)[v]\,Dg(x)[w]+Dg(x)[v]\,Df(x)[w].$$
--
--   This Leibniz rule for Hessians is used to compute second derivatives, and hence Laplacians, of products of smooth kernels, in particular of tensor products $f(x_1)g(x_2)$ on product spaces.
--
--   **Formalization Note** The second derivative is `hessianB h x = fderiv ℝ (fun y => fderiv ℝ h y) x`, applied first to $v$ and then to $w$; smoothness is `ContDiff ℝ (⊤ : ℕ∞)`. No completeness or finite-dimensionality of $E$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean#L45-L68

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian

open OAI OAI.EuclideanRamsey
universe uDomain uCodomain uIndex uColor uAction
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open scoped BigOperators
open Matrix MeasureTheory
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.EuclideanRamsey.hessianB_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v w : E) :
    hessianB (fun y => f y*g y) x v w =
      f x*hessianB g x v w + g x*hessianB f x v w +
      fderiv ℝ f x v*fderiv ℝ g x w + fderiv ℝ g x v*fderiv ℝ f x w := by sorry
