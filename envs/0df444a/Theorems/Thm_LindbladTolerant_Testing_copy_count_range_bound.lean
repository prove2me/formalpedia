-- Prove2me | Theorems.Thm_LindbladTolerant_Testing_copy_count_range_bound
-- name    : LindbladTolerant.Testing.copy_count_range_bound
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:57:16.241001+00:00
-- url     : https://prove2.me/theorems/74ca58c8-4000-4acc-b589-ffeda259a97f
-- title:
--   Explicit copy-count and clipped-output bounds for Theorem 4.3
-- statement:
--   For $k\ge1$, $n\ge1$, and $0<\delta\le1/16$, the ceiling-defined copy constant satisfies $C_k\ge1$, the three-batch estimator uses
--   $$S(k,\delta)=m+N+2s\le\lceil C_k\delta^{-2}\rceil$$
--   copies, and every output obeys $0\le\widehat h\le(2^k+1)/2$. This isolates the deterministic resource accounting and interval clipping in the proof of Theorem 4.3. The $+4$ in the explicit constant accounts for one extra copy from each of $m,N,s$ and one from doubling $s$.
--
--   **Formalization Note** `copyCount` and `copyConstant` are the published explicit definitions inferred from the batch sizes; no probabilistic correctness is assumed here.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, proof of Theorem 4.3, pp.22–23, PDF pp.22–23, batch definitions and final clipping

import Definitions.Def_LindbladTolerant_Testing_estimator

set_option autoImplicit false
open scoped ComplexOrder

theorem LindbladTolerant.Testing.copy_count_range_bound :
    ∀ k : ℕ, 1 ≤ k → 1 ≤ copyConstant k ∧
    ∀ n : ℕ, 1 ≤ n → ∀ delta : ℝ, 0 < delta → delta ≤ 1/16 →
      copyCount k delta ≤ ⌈copyConstant k * delta⁻¹^2⌉₊ ∧
      (∀ x : EstimatorSample n k delta,
        0 ≤ estimatorValue k delta x ∧ estimatorValue k delta x ≤ functionalBound k) := by sorry
