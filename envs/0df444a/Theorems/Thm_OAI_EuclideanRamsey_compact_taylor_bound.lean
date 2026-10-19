-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_compact_taylor_bound
-- name    : OAI.EuclideanRamsey.compact_taylor_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:05:39.226163+00:00
-- url     : https://prove2.me/theorems/ff408b69-e0d9-47ab-8ced-1dd85b136502
-- title:
--   Uniform cubic Taylor remainder bound for smooth compactly supported functions
-- statement:
--   Let $E$ be a real normed space and let $f:E\to\mathbb{R}$ be a $C^\infty$ function with compact support. Write $Df(x)$ for the Fréchet derivative of $f$ at $x$ and $D^2f(x)[h,h]$ for its second derivative at $x$ evaluated at $(h,h)$. Then there is a constant $K\ge0$ such that for all $x,h\in E$
--
--   $$
--   \Big|\,f(x+h)-f(x)-Df(x)[h]-\tfrac12\,D^2f(x)[h,h]\,\Big|\;\le\;K\,\|h\|^3 .
--   $$
--
--   Thus the second-order Taylor expansion of $f$ holds with a remainder of order $\|h\|^3$ that is uniform in the base point $x$: compact support makes the third derivative globally bounded. This uniformity is what makes finite-difference approximations of second-order differential operators applied to $f$ converge uniformly on the whole space.
--
--   **Formalization Note** The second derivative is `iteratedFDeriv ℝ 2 f x ![h, h]`, and smoothness is `ContDiff ℝ (⊤ : ℕ∞)`, i.e. $C^\infty$. $E$ is not assumed complete or finite-dimensional.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean#L23-L59

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
universe uDomain uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators

theorem OAI.EuclideanRamsey.compact_taylor_bound {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x h : E,
      |f (x+h)-f x-fderiv ℝ f x h-
        (1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h]| ≤ K*‖h‖^3 := by sorry
