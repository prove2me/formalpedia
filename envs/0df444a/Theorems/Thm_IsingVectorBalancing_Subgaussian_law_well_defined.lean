-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_law_well_defined
-- name    : IsingVectorBalancing.Subgaussian.law_well_defined
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T01:34:01.611688+00:00
-- url     : https://prove2.me/theorems/2ef4ae0a-3451-4a94-9487-97cc2026b6ad
-- title:
--   §1 / §6 — the product weights define a probability law
-- statement:
--   Let $v_1,\ldots,v_n\in\mathbb R^d$ satisfy $\|v_i\|_2\le1$, and suppose no three distinct indices carry parallel unit vectors (including equality up to sign). For $\sigma\in\Omega=\{-1,+1\}^n$ and $h\in\mathbb R^n$, put
--   $$w_v(\sigma)=\prod_{i<j}(1-\sigma_i\sigma_j\langle v_i,v_j\rangle),\quad
--   w_{v,h}(\sigma)=e^{\sum_i h_i\sigma_i}w_v(\sigma),\quad
--   Z_v(h)=\sum_{\sigma\in\Omega}w_{v,h}(\sigma).$$
--   Write $\mu_{v,h}(\sigma)=w_{v,h}(\sigma)/Z_v(h)$, $\mathbb E_h$ for its finite expectation, and $s_v(\sigma)=\sum_i\sigma_i v_i$.
--
--   For every real external field $h$,
--   $$w_{v,h}(\sigma)\ge0\quad(\sigma\in\Omega),\qquad Z_v(h)>0,\qquad
--   \mu_{v,h}(\sigma)\ge0,\qquad\sum_{\sigma\in\Omega}\mu_{v,h}(\sigma)=1.$$
--   This records the source's unnumbered well-definedness assertion and makes normalization a proof obligation. Individual zero weights remain allowed; positivity of the partition function is a conclusion rather than an extra premise.
--
--   Differences from the source:
--   - encoding: indices 1 through n, vectors in R^d, and signs in {-1,+1} → indices Fin n, EuclideanSpace over Fin d, and Bool configurations mapped to real signs; reason: coordinate relabelling is bijective and preserves the Euclidean inner product and every product weight
--   - generalization: the source does not discuss the empty input or zero dimensional boundary → n = 0 and d = 0 are included; reason: the empty cube has one configuration with weight 1 and signed sum zero, and in dimension zero all vectors and directions are zero; every positive dimensional nonempty source instance remains included
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, pp. 1, 4, 6 (PDF 2, 5, 7), §1 after Eq. (1), §4 opening, §6 after Eq. (6), unnumbered well-definedness assertion; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Law

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

/-- Unnumbered well-definedness assertion, §1 and §6 after (6). -/
theorem law_well_defined {n d : ℕ} (v : Fin n → Vec d) (hv : Admissible v)
    (h : Fin n → ℝ) :
    (∀ σ : Configuration n, 0 ≤ tiltedWeight v h σ) ∧
    0 < partition v h ∧
    (∀ σ : Configuration n, 0 ≤ probability v h σ) ∧
    (∑ σ : Configuration n, probability v h σ) = 1 := by sorry

end IsingVectorBalancing.Subgaussian
