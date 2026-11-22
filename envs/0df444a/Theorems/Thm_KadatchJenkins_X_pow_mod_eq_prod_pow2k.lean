-- Prove2me | Theorems.Thm_KadatchJenkins_X_pow_mod_eq_prod_pow2k
-- name    : KadatchJenkins.X_pow_mod_eq_prod_pow2k
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-21T22:01:43.152471+00:00
-- url     : https://prove2.me/theorems/1306fe31-374f-484e-b525-f555987366c1
-- title:
--   Eq. (5) — Powers of x from the binary expansion
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and let $\mathrm{Pow2k}(k) = x^{2^k} \bmod P$. For every natural number $N$ with binary expansion $N = \sum_k n_k2^k$,
--   $$x^N = \prod_{k:\ n_k \ne 0}x^{2^k} \qquad\text{and}\qquad x^N \bmod P = \Big(\prod_{k:\ n_k \ne 0}\mathrm{Pow2k}(k)\Big) \bmod P.$$
--   Moreover $x^N \bmod P$ is obtained by starting from $1 \bmod P$ and, for each $k$ with $n_k \ne 0$ in increasing order, multiplying by $\mathrm{Pow2k}(k)$ and reducing mod $P$, so that every multiplication is of two polynomials of degree less than $D$; and there are at most $\lfloor\log_2 N\rfloor + 1$ such $k$ (read as $1$ for $N = 0$).
--   (For $N = 0$ the product is empty and both sides are $1 \bmod P$.)
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 8, §4.4, eq. (5) (Computing powers of x)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem X_pow_mod_eq_prod_pow2k (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (N : ℕ) :
    (X : (ZMod 2)[X]) ^ N = (N.bitIndices.map fun k => (X : (ZMod 2)[X]) ^ (2 ^ k)).prod ∧
      X ^ N % P = (N.bitIndices.map (pow2k P)).prod % P ∧
      X ^ N % P = N.bitIndices.foldl (fun a k => (a * pow2k P k) % P) (1 % P) ∧
      N.bitIndices.length ≤ Nat.log 2 N + 1 := by
  sorry

end KadatchJenkins
