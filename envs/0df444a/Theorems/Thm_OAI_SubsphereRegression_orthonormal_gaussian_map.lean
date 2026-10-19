-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_orthonormal_gaussian_map
-- name    : OAI.SubsphereRegression.orthonormal_gaussian_map
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:13:20.165183+00:00
-- url     : https://prove2.me/theorems/b0915320-b876-41a2-8fe3-89ef5a535756
-- title:
--   Coordinates of a standard Gaussian vector along an orthonormal family are independent standard normals
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and let $\gamma_E$ be the standard Gaussian measure on $E$, i.e. the law of $\sum_k\xi_ke_k$ for an orthonormal basis $(e_k)$ of $E$ and independent standard normal variables $\xi_k$; equivalently, the probability measure with characteristic function $t\mapsto e^{-\|t\|^{2}/2}$. Let $u_0,\dots,u_{n-1}\in E$ be an orthonormal family. Then the image of $\gamma_E$ under the coordinate map $x\mapsto(\langle u_0,x\rangle,\dots,\langle u_{n-1},x\rangle)$ is the product of $n$ standard normal laws on $\mathbb{R}^{n}$:
--   $$\bigl(x\mapsto(\langle u_i,x\rangle)_{0\le i<n}\bigr)_{\#}\,\gamma_E=\mathcal{N}(0,1)^{\otimes n}.$$
--   In other words, if $X\sim\gamma_E$ then $\langle u_0,X\rangle,\dots,\langle u_{n-1},X\rangle$ are independent standard normal random variables.
--
--   This rotation invariance of the standard Gaussian is the first step in bounding the joint law of the inner products of a Gaussian vector with arbitrary linearly independent vectors: after Gram–Schmidt orthonormalization these inner products become an invertible linear image of independent standard normals.
--
--   **Formalization Note** $\gamma_E$ is Mathlib's `stdGaussian E` and $\mathcal{N}(0,1)$ is `gaussianReal 0 1`; the target measure is `Measure.pi` on plain functions `Fin n → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gaussian.lean#L18-L42

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.orthonormal_gaussian_map {n : ℕ} {u : Fin n → E} (hu : Orthonormal ℝ u) :
    (stdGaussian E).map (fun x => fun i => ⟪u i, x⟫) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by sorry
