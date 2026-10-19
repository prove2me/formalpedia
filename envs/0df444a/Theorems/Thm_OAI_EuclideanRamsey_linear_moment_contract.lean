-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_linear_moment_contract
-- name    : OAI.EuclideanRamsey.linear_moment_contract
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:06:09.96281+00:00
-- url     : https://prove2.me/theorems/43248107-9776-4262-9a83-6350e9db1922
-- title:
--   Weighted sums of a linear functional depend only on first moments
-- statement:
--   Let $k\in\mathbb{N}$, let $S$ be a finite index set, and for each $\gamma\in S$ let $q_\gamma\in\mathbb{R}$ be a weight and $v_\gamma=(v_{\gamma,1},\dots,v_{\gamma,k})\in\mathbb{R}^k$ a vector. Let $L:\mathbb{R}^k\to\mathbb{R}$ be a linear functional and $\mathbf{e}_1,\dots,\mathbf{e}_k$ the standard basis of $\mathbb{R}^k$. Then
--
--   $$
--   \sum_{\gamma\in S}q_\gamma\,L(v_\gamma)\;=\;\sum_{j=1}^k\Big(\sum_{\gamma\in S}q_\gamma\,v_{\gamma,j}\Big)\,L(\mathbf{e}_j).
--   $$
--
--   So the weighted sum of $L$ over the points $v_\gamma$ depends on the weighted configuration only through its first moments $\sum_\gamma q_\gamma v_{\gamma,j}$, and it vanishes when all first moments vanish. This is how the first-order Taylor terms $Db(x)[v_\gamma]$ drop out of a finite-difference stencil with vanishing first moments.
--
--   **Formalization Note** $S$ is a `Finset ι` for an arbitrary index type `ι`, $L$ is a continuous linear map `(Fin k → ℝ) →L[ℝ] ℝ` (every linear functional on $\mathbb{R}^k$ is continuous), and $\mathbf{e}_j$ is `Pi.single j 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean#L66-L80

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
open scoped BigOperators

theorem OAI.EuclideanRamsey.linear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) = ∑ j,(∑ γ ∈ S,q γ*v γ j)*L (Pi.single j 1) := by sorry
