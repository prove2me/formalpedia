-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_rationalize_convolution
-- name    : OAI.EuclideanRamsey.rationalize_convolution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:10:03.331515+00:00
-- url     : https://prove2.me/theorems/b9985653-25ee-4772-92c6-faa240f934b1
-- title:
--   A real kernel satisfying strict convolution inequalities can be replaced by a rational one
-- statement:
--   Let $G$ be an abelian group and $\mathbb{Q}[G]$ its rational group algebra, whose elements are finitely supported functions $\beta:G\to\mathbb{Q}$, with the convolution product $(\nu*\beta)(\delta)=\sum_{\gamma\in G}\nu(\gamma)\,\beta(\delta-\gamma)$. For $\beta\in\mathbb{Q}[G]$ let $m(\beta)=\sum_{\gamma\in G}\beta(\gamma)$ be its mass. Fix $\nu\in\mathbb{Q}[G]$, a weight function $w:G\to\mathbb{R}$, and real numbers $t$ and $\eta$. Let $a:G\to\mathbb{R}$ be a function with finite support, and set $(\nu*a)(\delta)=\sum_{\gamma\in\operatorname{supp}\nu}\nu(\gamma)\,a(\delta-\gamma)$. Assume
--
--   $$
--   0<\frac{\sum_{\gamma\in G}a(\gamma)}{t}\qquad\text{and}\qquad\sum_{\delta\in G}\max\big(-(\nu*a)(\delta),\,0\big)\,w(\delta)\;<\;\eta\,\frac{\sum_{\gamma\in G}a(\gamma)}{t}.
--   $$
--
--   Then there is $\beta\in\mathbb{Q}[G]$ with
--
--   $$
--   0<\frac{m(\beta)}{t}\qquad\text{and}\qquad\sum_{\delta\in G}\max\big(-(\nu*\beta)(\delta),\,0\big)\,w(\delta)\;<\;\eta\,\frac{m(\beta)}{t}.
--   $$
--
--   All these sums are finite: the summands vanish outside $\operatorname{supp}a$, respectively outside the sumset $\operatorname{supp}\nu+\operatorname{supp}a$ (and likewise with $\beta$ in place of $a$).
--
--   In words, a real-valued finitely supported kernel $a$ satisfying the two strict inequalities can be replaced by a rational one, because both conditions are strict and depend continuously on finitely many coefficients. No sign conditions on $t$, $\eta$ or $w$ are needed. The result is used to pass from a real discretization of a smooth bump to a rational lattice measure, so that the product $\nu*\beta$ stays in $\mathbb{Q}[G]$.
--
--   **Formalization Note** $\mathbb{Q}[G]$ is `AddMonoidAlgebra ℚ G` (with `[DecidableEq G]`), $m(\beta)$ is `b.coeff.sum fun _ q => q` cast to $\mathbb{R}$, and $(\nu*\beta)(\delta)$ is `(ν*b).coeff δ`. Finite support of $a$ is `Function.HasFiniteSupport a`. The sums over $G$ are written as `tsum`s; as just noted, they are genuine finite sums. Division follows Lean's convention $x/0=0$, so the hypothesis $0<\sum a/t$ forces $t\neq0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/RationalConvolution.lean#L133-L220

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

open OAI OAI.EuclideanRamsey
universe uGroup uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped BigOperators Pointwise

theorem OAI.EuclideanRamsey.rationalize_convolution {G : Type uGroup} [AddCommGroup G] [DecidableEq G]
    (ν : AddMonoidAlgebra ℚ G) (w : G → ℝ) (t η : ℝ)
    {a : G → ℝ} (ha : Function.HasFiniteSupport a)
    (hp : 0 < (∑' γ,a γ)/t)
    (hn : (∑' δ,max (-(∑ γ ∈ ν.coeff.support,(ν.coeff γ:ℝ)*a (δ-γ))) 0*w δ) <
      η*((∑' γ,a γ)/t)) :
    ∃ b : AddMonoidAlgebra ℚ G,
      0 < ((b.coeff.sum fun _ q => q : ℚ):ℝ)/t ∧
      (∑' δ,max (-((ν*b).coeff δ:ℝ)) 0*w δ) <
        η*(((b.coeff.sum fun _ q => q : ℚ):ℝ)/t) := by sorry
