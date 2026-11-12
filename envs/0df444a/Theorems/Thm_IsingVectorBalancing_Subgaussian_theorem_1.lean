-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_theorem_1
-- name    : IsingVectorBalancing.Subgaussian.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T01:33:58.08408+00:00
-- url     : https://prove2.me/theorems/d4e5e7c4-347a-4eab-b07e-e38c35eaa00a
-- title:
--   Theorem 1 — the explicit Ising signed sum is one-subgaussian
-- statement:
--   Let $v_1,\ldots,v_n\in\mathbb R^d$ satisfy $\|v_i\|_2\le1$, and suppose no three distinct indices carry parallel unit vectors (including equality up to sign). For $\sigma\in\Omega=\{-1,+1\}^n$ and $h\in\mathbb R^n$, put
--   $$w_v(\sigma)=\prod_{i<j}(1-\sigma_i\sigma_j\langle v_i,v_j\rangle),\quad
--   w_{v,h}(\sigma)=e^{\sum_i h_i\sigma_i}w_v(\sigma),\quad
--   Z_v(h)=\sum_{\sigma\in\Omega}w_{v,h}(\sigma).$$
--   Write $\mu_{v,h}(\sigma)=w_{v,h}(\sigma)/Z_v(h)$, $\mathbb E_h$ for its finite expectation, and $s_v(\sigma)=\sum_i\sigma_i v_i$.
--
--   At external field $h=0$, every direction $\theta\in\mathbb R^d$ satisfies the uncentered bound
--   $$\mathbb E_0\exp\bigl(\langle\theta,s_v\rangle\bigr)\le\exp(\|\theta\|_2^2/2).$$
--   This is the headline vector-balancing guarantee for the explicit product-weight distribution, with subgaussian scale exactly one. The zero-field law is centrally symmetric and its signed sum has mean zero. Unit-norm inputs and pairs of parallel unit vectors are retained.
--
--   Differences from the source:
--   - encoding: indices 1 through n, vectors in R^d, and signs in {-1,+1} → indices Fin n, EuclideanSpace over Fin d, and Bool configurations mapped to real signs; reason: coordinate relabelling is bijective and preserves the Euclidean inner product and every product weight
--   - generalization: the source does not discuss the empty input or zero dimensional boundary → n = 0 and d = 0 are included; reason: the empty cube has one configuration with weight 1 and signed sum zero, and in dimension zero all vectors and directions are zero; every positive dimensional nonempty source instance remains included
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 1 (PDF 2), Theorem 1, Eq. (1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

theorem theorem_1 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (θ : Vec d) :
    expectation v (fun _ => 0) (fun σ => Real.exp (inner ℝ θ (signedSum v σ))) ≤
      Real.exp (‖θ‖ ^ 2 / 2) := by sorry

end IsingVectorBalancing.Subgaussian
