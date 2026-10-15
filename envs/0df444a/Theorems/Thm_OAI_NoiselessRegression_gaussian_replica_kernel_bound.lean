-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_gaussian_replica_kernel_bound
-- name    : OAI.NoiselessRegression.gaussian_replica_kernel_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:26:14.38799+00:00
-- url     : https://prove2.me/theorems/c4ea5bdf-aff9-4f00-a3ee-584466f62c8e
-- title:
--   Gaussian replica kernel bound in terms of Gram–Schmidt lengths
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and let $\gamma_E$ be the standard Gaussian measure on $E$ (the law of $\sum_k \xi_k e_k$ for an orthonormal basis $(e_k)$ of $E$ and independent standard normal variables $\xi_k$). For $m\in\mathbb N$, a design $A=(A_1,\dots,A_m)\in E^m$ is drawn from $\gamma_E^{\otimes m}$, i.e. it has independent standard Gaussian rows $A_j\in E$, and $dy$ denotes Lebesgue measure on $\mathbb R^m$.
--
--   Fix a point $p\in E$ and vectors $v_1,\dots,v_n\in E$ such that the differences $u_i=v_i-p$ $(1\le i\le n)$ are linearly independent, and let $w_1,\dots,w_n$ be their Gram–Schmidt orthogonalization without normalization: $w_i=u_i-\Pi_{i-1}u_i$, where $\Pi_{i-1}$ is the orthogonal projection onto $\operatorname{span}(u_1,\dots,u_{i-1})$. Let $\varphi:\mathbb R\to[0,\infty]$ be measurable with $\int_{\mathbb R}\varphi(z)\,dz=1$. Then
--
--   $$
--   \int_{E^m}\int_{\mathbb R^m}\Big(\prod_{j=1}^{m}\varphi\big(y_j-\langle p,A_j\rangle\big)\Big)\prod_{i=1}^{n}\prod_{j=1}^{m}\varphi\big(y_j-\langle v_i,A_j\rangle\big)\,dy\,d\gamma_E^{\otimes m}(A)\;\le\;\Big(\prod_{i=1}^{n}\|w_i\|\Big)^{-m}.
--   $$
--
--   Linear independence makes every $\|w_i\|$ positive. Recall that $\prod_i\|w_i\|=\sqrt{\det\big(\langle u_i,u_k\rangle\big)_{i,k=1}^{n}}$ is the $n$-dimensional volume of the parallelepiped spanned by $v_1-p,\dots,v_n-p$.
--
--   If $\varphi$ is the density of label noise, the integrand is the product of the label densities of the $n+1$ "replica" parameters $t=p,v_1,\dots,v_n$ observed through the same Gaussian design. The bound says that their overlap, averaged over the design, is at most the inverse $m$-th power of the volume spanned by the replicas, uniformly over all noise densities $\varphi$. It is the pointwise kernel estimate behind moment bounds for smoothed Gaussian projection laws.
--
--   **Formalization Note** All integrals are lower Lebesgue integrals of $[0,\infty]$-valued functions. The right-hand side is the real number $(\prod_i\|w_i\|)^{-m}$ embedded in $[0,\infty]$, and $w_i$ is Mathlib's `gramSchmidt` applied to the family $i\mapsto v_i-p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/GaussianKernel.lean#L209-L238

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.gaussian_replica_kernel_bound {n : ℕ} (p : E) (v : Fin n → E)
    (hv : LinearIndependent ℝ (fun i => v i - p))
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (hφ1 : ∫⁻ z, φ z = 1) (m : ℕ) :
    ∫⁻ A : Fin m → E, ∫⁻ y : Fin m → ℝ,
      (∏ j, φ (y j - ⟪p, A j⟫)) * ∏ i, ∏ j, φ (y j - ⟪v i, A j⟫)
      ∂volume ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ (fun i => v i - p) i‖)⁻¹ ^ m) := by sorry
