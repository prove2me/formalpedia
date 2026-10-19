-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_hessianB_linear_comp
-- name    : OAI.EuclideanRamsey.hessianB_linear_comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T01:59:24.153122+00:00
-- url     : https://prove2.me/theorems/937b6d42-5838-487e-a156-77aacd007f0b
-- title:
--   Second derivative of a smooth function composed with a continuous linear map
-- statement:
--   Let $E$ and $F$ be real normed spaces. For a function $f:F\to\mathbb{R}$ and $y\in F$, write $D^2f(y)$ for the derivative at $y$ of the map $z\mapsto Df(z)$, regarded as a bilinear form: $D^2f(y)[v,w]=\bigl(D(Df)(y)[v]\bigr)[w]$. Let $f$ be infinitely differentiable and $L:E\to F$ a continuous linear map. Then for all $x,v,w\in E$
--   $$D^2(f\circ L)(x)[v,w]=D^2f(Lx)[Lv,Lw].$$
--
--   This is the change-of-variables rule for Hessians under linear maps. It is used with coordinate projections of product spaces and with linear splittings of a space, for instance to compute second derivatives of functions of the form $f(x_1)g(x_2)$ on $E\times F$.
--
--   **Formalization Note** The bilinear second derivative is `hessianB f x = fderiv ℝ (fun y => fderiv ℝ f y) x : E →L[ℝ] E →L[ℝ] ℝ`, smoothness is `ContDiff ℝ (⊤ : ℕ∞) f`, and `L : E →L[ℝ] F`. No completeness or finite-dimensionality is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean#L29-L43

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

theorem OAI.EuclideanRamsey.hessianB_linear_comp {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (x v w : E) :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by sorry
