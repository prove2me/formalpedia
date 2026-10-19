-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_hessianB_prod_vertical
-- name    : OAI.EuclideanRamsey.hessianB_prod_vertical
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:01:36.184341+00:00
-- url     : https://prove2.me/theorems/bd726cdb-6782-444d-8673-78098873385a
-- title:
--   Hessian of a product $f(y_1)\,g(y_2)$ in the directions of the second factor
-- statement:
--   Let $E$ and $F$ be real normed spaces. For a function $\varphi : X\to\mathbb{R}$ on a real normed space $X$ and a point $x\in X$, write $D^2\varphi(x)$ for the second Fréchet derivative of $\varphi$ at $x$, that is, the derivative at $x$ of the map $y\mapsto D\varphi(y)$, regarded as a continuous bilinear form on $X$. Let $f : E\to\mathbb{R}$ and $g : F\to\mathbb{R}$ be $C^\infty$ functions, and let $f\otimes g : E\times F\to\mathbb{R}$ be the product function $(f\otimes g)(y_1,y_2)=f(y_1)\,g(y_2)$. Then for every point $x=(x_1,x_2)\in E\times F$ and all vectors $v,w\in F$,
--
--   $$
--   D^2(f\otimes g)(x)\big[(0,v),(0,w)\big] \;=\; f(x_1)\,D^2 g(x_2)[v,w].
--   $$
--
--   In words: along directions that move only the second factor, the Hessian of a tensor-product function is the Hessian of the second factor, scaled by the value of the first factor. Together with the analogous formula for directions in the first factor, this computes second-order differential operators applied to product bumps $f(y_1)g(y_2)$ block by block, after a linear change of coordinates that splits the space into a horizontal and a vertical part.
--
--   **Formalization Note** The second derivative is `hessianB φ x = fderiv ℝ (fun y => fderiv ℝ φ y) x`, of type `X →L[ℝ] X →L[ℝ] ℝ`. Smoothness is `ContDiff ℝ (⊤ : ℕ∞)`, i.e. $C^\infty$ (not analyticity). No completeness or finite-dimensionality of $E$ or $F$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean#L87-L102

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

theorem OAI.EuclideanRamsey.hessianB_prod_vertical {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : F) :
    hessianB (fun x : E × F => f x.1*g x.2) x (0,v) (0,w) =
      f x.1*hessianB g x.2 v w := by sorry
