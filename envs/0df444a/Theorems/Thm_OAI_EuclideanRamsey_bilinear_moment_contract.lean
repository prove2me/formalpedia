-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_bilinear_moment_contract
-- name    : OAI.EuclideanRamsey.bilinear_moment_contract
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:06:51.062174+00:00
-- url     : https://prove2.me/theorems/e744651e-f783-4ae3-adf8-2b194b230a44
-- title:
--   Weighted sums of a bilinear form on the diagonal depend only on second moments
-- statement:
--   Let $k\in\mathbb{N}$, let $S$ be a finite index set, and for each $\gamma\in S$ let $q_\gamma\in\mathbb{R}$ and $v_\gamma=(v_{\gamma,1},\dots,v_{\gamma,k})\in\mathbb{R}^k$. Let $L:\mathbb{R}^k\times\mathbb{R}^k\to\mathbb{R}$ be a bilinear form and $\mathbf e_1,\dots,\mathbf e_k$ the standard basis of $\mathbb{R}^k$. Then
--
--   $$
--   \sum_{\gamma\in S}q_\gamma\,L(v_\gamma,v_\gamma)\;=\;\sum_{j=1}^k\sum_{l=1}^k\Big(\sum_{\gamma\in S}q_\gamma\,v_{\gamma,j}\,v_{\gamma,l}\Big)\,L(\mathbf e_j,\mathbf e_l).
--   $$
--
--   So the weighted sum of the quadratic form $v\mapsto L(v,v)$ over the points $v_\gamma$ depends only on the second-moment matrix $\big(\sum_\gamma q_\gamma v_{\gamma,j}v_{\gamma,l}\big)_{j,l}$. Applied to a Hessian $L=D^2b(x)$, it identifies the second-order Taylor term of a finite-difference stencil with $\sum_{j,l}C_{jl}\,\partial_j\partial_lb(x)$, where $C$ is the second-moment matrix of the stencil.
--
--   **Formalization Note** $L$ is a continuous bilinear map `(Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ` (every bilinear form on $\mathbb{R}^k$ is continuous), $S$ is a `Finset ι` for an arbitrary index type, and $\mathbf e_j$ is `Pi.single j 1`. No symmetry of $L$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean#L82-L108

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

theorem OAI.EuclideanRamsey.bilinear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) (v γ) =
      ∑ j,∑ l,(∑ γ ∈ S,q γ*v γ j*v γ l)*L (Pi.single j 1) (Pi.single l 1) := by sorry
