-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_hessianB_prod_horizontal
-- name    : OAI.EuclideanRamsey.hessianB_prod_horizontal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:00:56.431992+00:00
-- url     : https://prove2.me/theorems/8e5daf54-1793-41bb-a004-3fd7898bff45
-- title:
--   Horizontal second derivative of a product $f(x_1)\,g(x_2)$ on a product space
-- statement:
--   Let $E$ and $F$ be real normed spaces and let $f:E\to\mathbb{R}$ and $g:F\to\mathbb{R}$ be infinitely differentiable. On the product $E\times F$ consider $h(y_1,y_2)=f(y_1)\,g(y_2)$. For a function $u$ write $D^2u(x)[v,w]$ for its second Fréchet derivative at $x$, the derivative of $y\mapsto Du(y)$ at $x$ regarded as a bilinear form. Then for every point $x=(x_1,x_2)\in E\times F$ and all horizontal directions $(v,0),(w,0)$ with $v,w\in E$,
--   $$D^2h(x)\bigl[(v,0),(w,0)\bigr]=g(x_2)\,D^2f(x_1)[v,w].$$
--
--   In directions tangent to the first factor, the Hessian of a product kernel is the Hessian of $f$ scaled by the value of $g$. This is used to compute Laplacians of product smoothing kernels on a space split into two complementary parts.
--
--   **Formalization Note** The second derivative is `hessianB` (`fderiv` of `fderiv`), smoothness is `ContDiff ℝ (⊤ : ℕ∞)`, and $E\times F$ carries the product normed-space structure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean#L70-L85

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

theorem OAI.EuclideanRamsey.hessianB_prod_horizontal {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : E) :
    hessianB (fun x : E × F => f x.1*g x.2) x (v,0) (w,0) =
      g x.2*hessianB f x.1 v w := by sorry
