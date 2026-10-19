-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_bilinear_matrix_pushforward
-- name    : OAI.EuclideanRamsey.bilinear_matrix_pushforward
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:02:33.397633+00:00
-- url     : https://prove2.me/theorems/c65ff863-ef17-4892-b166-d33455a17040
-- title:
--   Pairing a bilinear form with $MDM^{\top}$ equals pairing $D$ with the form on the columns of $M$
-- statement:
--   Let $k,n\in\mathbb{N}$, let $B:\mathbb{R}^k\times\mathbb{R}^k\to\mathbb{R}$ be a continuous bilinear form, and write $\mathbf{e}_1,\dots,\mathbf{e}_k$ for the standard basis vectors of $\mathbb{R}^k$. Let $M$ be a real $k\times n$ matrix with columns $M_{\cdot 1},\dots,M_{\cdot n}\in\mathbb{R}^k$, and let $D$ be a real $n\times n$ matrix. Then
--
--   $$
--   \sum_{j=1}^{k}\sum_{l=1}^{k}\big(MDM^{\top}\big)_{jl}\,B(\mathbf{e}_j,\mathbf{e}_l)\;=\;\sum_{a=1}^{n}\sum_{b=1}^{n}D_{ab}\,B\big(M_{\cdot a},M_{\cdot b}\big).
--   $$
--
--   The left side pairs $B$ with the matrix $MDM^{\top}$ in standard coordinates; the identity rewrites it as a pairing of $D$ with the values of $B$ on the columns of $M$. Applied to a Hessian $B=D^2h(x)$, it turns a second-order expression $\sum_{j,l}C_{jl}\,\partial_j\partial_l h(x)$ with a factored coefficient matrix $C=MDM^{\top}$ into second derivatives along the columns of $M$; for instance, with $D$ the identity, $\sum_{j,l}(MM^{\top})_{jl}\,\partial_j\partial_l h(x)=\sum_a D^2h(x)[M_{\cdot a},M_{\cdot a}]$.
--
--   **Formalization Note** $B$ has type `(Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ`, the basis vector $\mathbf{e}_j$ is `Pi.single j 1`, and the column $M_{\cdot a}$ is `fun j => M j a`. No symmetry of $B$ or $D$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean#L162-L190

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

theorem OAI.EuclideanRamsey.bilinear_matrix_pushforward {k n : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ)
    (M : Matrix (Fin k) (Fin n) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    ∑ j, ∑ l, (M*D*M.transpose) j l * B (Pi.single j 1) (Pi.single l 1) =
      ∑ a, ∑ b, D a b * B (fun j => M j a) (fun j => M j b) := by sorry
