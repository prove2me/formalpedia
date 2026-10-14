-- Prove2me | Theorems.Thm_IntMul_HvdH_chunk_product
-- name    : IntMul.HvdH.chunk_product
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:37:23.526887+00:00
-- url     : https://prove2.me/theorems/b10ded68-7972-409b-9ba4-10e16e8d925d
-- title:
--   Chunking: $fg=(FG)(2^b)$ with coefficients below $N2^{2b}$
-- statement:
--   **Splitting into chunks.** Let $b\ge0$, $N\ge1$ and $0\le f,g<2^{bN}$. Write the base-$2^b$ digits $F_k=\lfloor f/2^{bk}\rfloor\bmod 2^b$ and $G_k=\lfloor g/2^{bk}\rfloor\bmod 2^b$ for $0\le k<N$, and $F_k=G_k=0$ for $k\ge N$. Put
--   $$H_j=\sum_{k=0}^{j}F_kG_{j-k}.$$
--   Then
--   $$fg=\sum_{j=0}^{2N-2}H_j\,2^{bj},\qquad 0\le H_j<N\,2^{2b}\ \text{ for every } j.$$
--
--   This is step (1) of Proposition 5.4: with $F(x)=\sum_kF_kx^k$ and $G(x)=\sum_kG_kx^k$ we have $f=F(2^b)$, $g=G(2^b)$, and $fg=(FG)(2^b)$, whose coefficients $H_j$ are small enough to be recovered exactly and recombined by overlap-add.
--
--   **Formalization Note** All quantities are natural numbers; the digits are written with `/` and `%`.
-- source:
--   D. Harvey and J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193 (2021), no. 2, 563–617, https://doi.org/10.4007/annals.2021.193.2.4, §5.3 proof of Proposition 5.4, step (1) (split f, g into N chunks of b bits, f = F(2^b), g = G(2^b), fg = (FG)(2^b), 0 ≤ H_j < 2^{2b} N)

import Mathlib
open Finset

namespace IntMul.HvdH

theorem chunk_product (b N f g : ℕ) (hN : 1 ≤ N) (hf : f < 2 ^ (b * N)) (hg : g < 2 ^ (b * N)) :
    f * g = ∑ j ∈ range (2 * N - 1),
        (∑ k ∈ range (j + 1),
          (if k < N then f / 2 ^ (b * k) % 2 ^ b else 0) *
          (if j - k < N then g / 2 ^ (b * (j - k)) % 2 ^ b else 0)) * 2 ^ (b * j) ∧
    ∀ j, (∑ k ∈ range (j + 1),
          (if k < N then f / 2 ^ (b * k) % 2 ^ b else 0) *
          (if j - k < N then g / 2 ^ (b * (j - k)) % 2 ^ b else 0)) < N * 2 ^ (2 * b) := by sorry

end IntMul.HvdH
