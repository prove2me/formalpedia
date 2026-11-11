-- Prove2me | Theorems.Thm_LindbladShallow_lemma_4_10
-- name    : LindbladShallow.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:12:45.084231+00:00
-- url     : https://prove2.me/theorems/c2007a1d-2630-4d50-8db3-c114b2816ba2
-- title:
--   Lemma 4.10 — smoothed coefficients
-- statement:
--   Let $q\ge1$, $p(z)=(z^2+z^4)/2$, $p(z)^q=\sum_kc_kz^k$ and $\lambda_N=\frac N{6q}(c_{N-6q}-c_N)$ for $1\le N\le10q$. Then, with $g_N(z)=\frac1N\sum_{j<N}z^j$,
--   $$\sum_{N=1}^{10q}\lambda_Ng_N(z)=p(z)^qg_{6q}(z),\qquad \sum_N\lambda_N=1,\qquad \sum_N|\lambda_N|=2.$$
--
--   These coefficients combine finite-reuse lengths so that the residual contains the contracting polynomial $p(S_{11})^q$.
--
--   Differences from the source:
--   - encoding: an identity in z → an identity of polynomials over ℚ; reason: equivalent to the identity for every z
--   - encoding: c_{N−6q} with absent coefficients zero → 0 when N < 6q; reason: natural-number subtraction guard
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 4.10, p.34, Eq. (28); g_N from Eq. (18), p.23

import Mathlib
import Definitions.Def_LindbladShallow_smoothCoeff

open Polynomial

namespace LindbladShallow

/-- **Lemma 4.10** (Smoothed coefficients; arXiv:2610.05362, held version sha256 8f4637ef…,
p.34). Let `q ≥ 1`, `p(z) := (z² + z⁴)/2`, `p(z)^q = Σ_k c_k z^k` (absent coefficients zero), and
`λ_N := (N/(6q))(c_{N−6q} − c_N)` for `1 ≤ N ≤ 10q`. Then
`Σ_N λ_N g_N(z) = p(z)^q g_{6q}(z)`, `Σ_N λ_N = 1` and `Σ_N |λ_N| = 2` (28), sums over
`1 ≤ N ≤ 10q`, with `g_N(z) = (1/N) Σ_{j<N} z^j`.

**Formalization Note** The first identity is an identity of polynomials over `ℚ`. -/
theorem lemma_4_10 (q : ℕ) (hq : 1 ≤ q) :
    ∑ N ∈ Finset.Icc 1 (10 * q), C (lamN q N) * gPoly N = pPoly ^ q * gPoly (6 * q) ∧
      ∑ N ∈ Finset.Icc 1 (10 * q), lamN q N = 1 ∧
      ∑ N ∈ Finset.Icc 1 (10 * q), |lamN q N| = 2 := by sorry

end LindbladShallow
