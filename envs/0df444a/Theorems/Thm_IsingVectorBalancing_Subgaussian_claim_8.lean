-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_claim_8
-- name    : IsingVectorBalancing.Subgaussian.claim_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:34:09.060413+00:00
-- url     : https://prove2.me/theorems/d0e0d3c0-ea94-4081-bc65-f5028538eb65
-- title:
--   Claim 8 — gradient and Hessian of the log partition function
-- statement:
--   Let $v_1,\ldots,v_n\in\mathbb R^d$ satisfy $\|v_i\|_2\le1$, and suppose no three distinct indices carry parallel unit vectors (including equality up to sign). For $\sigma\in\Omega=\{-1,+1\}^n$ and $h\in\mathbb R^n$, put
--   $$w_v(\sigma)=\prod_{i<j}(1-\sigma_i\sigma_j\langle v_i,v_j\rangle),\quad
--   w_{v,h}(\sigma)=e^{\sum_i h_i\sigma_i}w_v(\sigma),\quad
--   Z_v(h)=\sum_{\sigma\in\Omega}w_{v,h}(\sigma).$$
--   Write $\mu_{v,h}(\sigma)=w_{v,h}(\sigma)/Z_v(h)$, $\mathbb E_h$ for its finite expectation, and $s_v(\sigma)=\sum_i\sigma_i v_i$.
--
--   Let $F_v(h)=\log Z_v(h)$. For every external field, its actual first and second derivatives satisfy
--   $$\frac{\partial F_v}{\partial h_i}(h)=\mathbb E_h[\sigma_i],\qquad
--   \frac{\partial^2F_v}{\partial h_j\partial h_i}(h)=\mathbb E_h[\sigma_i\sigma_j]-\mathbb E_h[\sigma_i]\mathbb E_h[\sigma_j].$$
--   Both derivative identities are asserted. They identify the response of the log partition function to the external field and supply the covariance matrix used in the concentration result.
--
--   **Formalization Note** The first Fréchet derivative is the continuous linear functional with the displayed mean coefficients. For every coordinate $i$, the Fréchet derivative of $h\mapsto DF_v(h)[e_i]$ is the functional with covariance row $i$. Thus differentiability is asserted, rather than inferred from a total derivative operator's default value.
--
--   Differences from the source:
--   - encoding: indices 1 through n, vectors in R^d, and signs in {-1,+1} → indices Fin n, EuclideanSpace over Fin d, and Bool configurations mapped to real signs; reason: coordinate relabelling is bijective and preserves the Euclidean inner product and every product weight
--   - generalization: the source does not discuss the empty input or zero dimensional boundary → n = 0 and d = 0 are included; reason: the empty cube has one configuration with weight 1 and signed sum zero, and in dimension zero all vectors and directions are zero; every positive dimensional nonempty source instance remains included
--   - encoding: gradient and Hessian matrices → the first Fréchet derivative and derivatives of its coordinate components; reason: coordinate projections identify the two linear maps with exactly the displayed gradient and Hessian, with no added regularity premise
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 8 (PDF 9), proof p. 9 (PDF 10), Claim 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

/-- Both actual derivatives: the gradient and every row of the Hessian. -/
theorem claim_8 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) :
    HasFDerivAt (logPartition v)
      (∑ i : Fin n, expectation v h (fun σ => spin (σ i)) •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) h ∧
    (∀ i : Fin n,
      HasFDerivAt (fun h' : Fin n → ℝ =>
        fderiv ℝ (logPartition v) h' (Pi.single i 1))
        (∑ j : Fin n, spinCovariance v h i j •
          (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) h) := by sorry

end IsingVectorBalancing.Subgaussian
