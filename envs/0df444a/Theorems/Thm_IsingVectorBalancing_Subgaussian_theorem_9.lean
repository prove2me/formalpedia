-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_theorem_9
-- name    : IsingVectorBalancing.Subgaussian.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T01:34:15.446353+00:00
-- url     : https://prove2.me/theorems/fbbf73d6-2cb4-4bc5-892c-5212c0a1c567
-- title:
--   Theorem 9 — centered one-subgaussian bound under every external field
-- statement:
--   Let $v_1,\ldots,v_n\in\mathbb R^d$ satisfy $\|v_i\|_2\le1$, and suppose no three distinct indices carry parallel unit vectors (including equality up to sign). For $\sigma\in\Omega=\{-1,+1\}^n$ and $h\in\mathbb R^n$, put
--   $$w_v(\sigma)=\prod_{i<j}(1-\sigma_i\sigma_j\langle v_i,v_j\rangle),\quad
--   w_{v,h}(\sigma)=e^{\sum_i h_i\sigma_i}w_v(\sigma),\quad
--   Z_v(h)=\sum_{\sigma\in\Omega}w_{v,h}(\sigma).$$
--   Write $\mu_{v,h}(\sigma)=w_{v,h}(\sigma)/Z_v(h)$, $\mathbb E_h$ for its finite expectation, and $s_v(\sigma)=\sum_i\sigma_i v_i$.
--
--   For every real external field $h$ and direction $\theta\in\mathbb R^d$,
--   $$\mathbb E_h\exp\bigl(\langle\theta,s_v-\mathbb E_h s_v\rangle\bigr)
--   \le\exp(\|\theta\|_2^2/2).$$
--   The centering uses the mean under the law with that very field $h$. The subgaussian scale is exactly one, with no dependence on the dimension, input family, or field. This strengthens the zero-field balancing guarantee while retaining its sharp constant.
--
--   Differences from the source:
--   - encoding: indices 1 through n, vectors in R^d, and signs in {-1,+1} → indices Fin n, EuclideanSpace over Fin d, and Bool configurations mapped to real signs; reason: coordinate relabelling is bijective and preserves the Euclidean inner product and every product weight
--   - generalization: the source does not discuss the empty input or zero dimensional boundary → n = 0 and d = 0 are included; reason: the empty cube has one configuration with weight 1 and signed sum zero, and in dimension zero all vectors and directions are zero; every positive dimensional nonempty source instance remains included
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 9 (PDF 10), Theorem 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

theorem theorem_9 {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) (θ : Vec d) :
    expectation v h (fun σ => Real.exp (inner ℝ θ (signedSum v σ - meanSum v h))) ≤
      Real.exp (‖θ‖ ^ 2 / 2) := by sorry

end IsingVectorBalancing.Subgaussian
