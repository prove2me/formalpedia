-- Prove2me | Theorems.Thm_GaussianMatrix_gaussian_integration_by_parts
-- name    : GaussianMatrix.gaussian_integration_by_parts
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T07:44:32.537986+00:00
-- url     : https://prove2.me/theorems/6607ec25-3e71-4bba-8073-ce3781ea7e67
-- title:
--   Gaussian integration by parts: $\mathbb E[U\,G(V)]=\sum_j \mathrm{Cov}(U,V_j)\,\mathbb E[\partial_j G(V)]$ for jointly Gaussian $(U,V)$, $U$ centered, $G\in C^1_b$
-- statement:
--   Let $\iota$ be a finite index set and let $(\Omega,P)$ be a probability space. Let $U:\Omega\to\mathbb R$ and $V=(V_j)_{j\in\iota}:\Omega\to\mathbb R^\iota$ be random variables such that the pair $(U,V)$ has a Gaussian law on $\mathbb R\times\mathbb R^\iota$, and suppose $U$ is centered: $\mathbb E\,U=0$. Let $G:\mathbb R^\iota\to\mathbb R$ be differentiable everywhere, with partial derivatives $G'_j=\partial_jG$. Assume each $G'_j$ is continuous, and that for some constant $C$ we have $|G|\le C$ and $|G'_j|\le C$ for all $j$. Then
--   $$\mathbb E\,\big[U\,G(V)\big]=\sum_{j\in\iota}\operatorname{Cov}(U,V_j)\;\mathbb E\,\big[\partial_jG(V)\big].$$
--
--   This is the Gaussian integration-by-parts (Stein) identity. It drives Gaussian interpolation arguments: the Sudakov–Fernique and Slepian comparison inequalities, Gordon's inequality, and Chatterjee's error bounds. In those arguments one differentiates $\theta\mapsto\mathbb E\,F(Z(\theta))$ along an interpolating Gaussian path $Z(\theta)$ and turns $\mathbb E[Z'_i\,\partial_iF(Z)]$ into covariances times second derivatives. Here the identity is proved by regressing $V$ on $U$. The residual $V-cU$ is uncorrelated with $U$, hence independent of it, which reduces the claim to the one-dimensional identity $\mathbb E[\xi h(\xi)]=v\,\mathbb E[h'(\xi)]$ for $\xi\sim N(0,v)$.
--
--   **Formalization Note.** Joint Gaussianity is `HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P`; this also forces $P$ to be a probability measure. The gradient is supplied explicitly: `HasFDerivAt G (∑ j, G' j x • proj j) x`, i.e. $DG(x)v=\sum_j G'_j(x)v_j$. The covariance is Mathlib's `cov[U, V j; P]`. Edge cases: if $\operatorname{Var}U=0$, both sides are $0$; if $\iota=\emptyset$, $G$ is constant and both sides are $0$ because $\mathbb E\,U=0$. The boundedness of $G$ and $\nabla G$ is a convenient sufficient regularity class ($C^1_b$); it makes every integral finite, so the Bochner convention for non-integrable functions plays no role.
-- source:
--   R. Vershynin, High-Dimensional Probability (Cambridge Univ. Press, 2018), Lemma 7.2.3 (Gaussian integration by parts) and Exercise 7.2.4 (multivariate version); see also S. Chatterjee, 'An error bound in the Sudakov–Fernique inequality', arXiv:math/0510424, Lemma 1 (Gaussian integration by parts). Numbering from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem gaussian_integration_by_parts {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} (U : Ω → ℝ) (V : ι → Ω → ℝ)
    (hUV : HasGaussianLaw (fun ω => (U ω, fun j => V j ω)) P) (hU0 : ∫ ω, U ω ∂P = 0)
    (G : (ι → ℝ) → ℝ) (G' : ι → (ι → ℝ) → ℝ)
    (hG : ∀ x, HasFDerivAt G
      (∑ j, G' j x • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x)
    (hG'c : ∀ j, Continuous (G' j)) (C : ℝ) (hGb : ∀ x, |G x| ≤ C)
    (hG'b : ∀ j x, |G' j x| ≤ C) :
    ∫ ω, U ω * G (fun j => V j ω) ∂P = ∑ j, cov[U, V j; P] * ∫ ω, G' j (fun j => V j ω) ∂P := by sorry

end GaussianMatrix
