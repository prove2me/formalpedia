-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_exists_singular_pair
-- name    : OAI.DirectCrouzeix.exists_singular_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:27:12.109832+00:00
-- url     : https://prove2.me/theorems/29e1aeb8-e5d0-4c51-8997-56d883ea482e
-- title:
--   Top singular pair of an operator on a finite-dimensional complex Hilbert space
-- statement:
--   Let $\iota$ be a nonempty finite index set and $H=\mathbb{C}^{\iota}$ with inner product $\langle x,y\rangle=\sum_i\overline{x_i}\,y_i$ and the Euclidean norm. Let $T:H\to H$ be a linear operator whose operator norm $\|T\|=\sup_{\|x\|\le1}\|Tx\|$ is positive, and let $T^*$ be its adjoint, characterized by $\langle T^*y,x\rangle=\langle y,Tx\rangle$. Then there exist unit vectors $x,y\in H$ such that
--   $$Tx=\|T\|\,y\qquad\text{and}\qquad T^*y=\|T\|\,x .$$
--
--   In other words, $\|T\|$ is a singular value of $T$ with right singular vector $x$ and left singular vector $y$, and $\langle y,Tx\rangle=\|T\|$. Such a pair converts the norm of an operator into a single matrix coefficient together with two exact relations; it is applied to the Kronecker-product operator $\sum_kA^k\otimes B_k$ on $\mathbb{C}^n\otimes\mathbb{C}^m$ in order to test its norm against one well-chosen pair of vectors.
--
--   **Formalization Note** $T$ is a continuous linear map on `EuclideanSpace ℂ ι`, the real number $\|T\|$ is cast to a complex scalar, and the adjoint is `ContinuousLinearMap.adjoint T`. Nonemptiness of $\iota$ is an explicit hypothesis (it also follows from $\|T\|>0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SingularPairs.lean#L51-L78

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs

open OAI OAI.DirectCrouzeix
universe u_37 u_38 u_39 u_40
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.exists_singular_pair {ι : Type u_38} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hT : 0 < ‖T‖) :
    ∃ x y : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      T x = (‖T‖ : ℂ) • y ∧
      ContinuousLinearMap.adjoint T y = (‖T‖ : ℂ) • x := by sorry
