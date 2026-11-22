-- Prove2me | Theorems.Thm_KadatchJenkins_crc0_interleaved
-- name    : KadatchJenkins.crc0_interleaved
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:14:31.663982+00:00
-- url     : https://prove2.me/theorems/ecaae2d1-190b-4921-9f7e-2d13a9a89cd3
-- title:
--   Eqs. (19)–(20) — Correctness of the interleaved word-by-word CRC
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $W \ge 0$, $N \ge 1$, $K \ge 0$, and let $m_{k,n}$ ($k, n \ge 0$) be $W$-bit words; only those with $k \le K$ and $n < N$ enter. Let $g_k = m_{k,0} \dots m_{k,N-1}$, let $M = g_0 \dots g_{K-1}$ be the message of the first $K$ groups, and let $M g_K$ be $M$ followed by $g_K$, that is $m_{0,0} \dots m_{0,N-1}\,m_{1,0} \dots m_{K,N-1}$. For a polynomial $v(x)$, let $v_{k,n}$ be the stripe CRCs computed by the recurrence (17):
--   $$v_{0,0} = v, \qquad v_{0,n} = 0 \ (n \ge 1), \qquad v_{k+1,n} = \mathrm{CrcWordN}(m_{k,n}, v_{k,n}),$$
--   with $\mathrm{CrcWordN}(m, v) = \big((v\,x^W + m(x)\,x^D)\,x^{(N-1)W}\big) \bmod P$. Then
--   $$\mathrm{CRC}_0(M g_K, v) = \Big(\sum_{n=0}^{N-1}\big(v_{K,n}\,x^W + m_{K,n}(x)\,x^D\big)\,x^{(N-1-n)W}\Big) \bmod P \qquad (19)$$
--   and
--   $$\mathrm{CRC}_0(M g_K, v) = \Big(\sum_{n=0}^{N-1}\mathrm{CRC}_0(m_{K,n}, v_{K,n})\,x^{(N-1-n)W}\Big) \bmod P. \qquad (20)$$
--
--   Kadatch–Jenkins, p. 19, §4.11.2: “There is more efficient and elegant solution. Assume that $M(x)$ is followed by one more group $g_K(x)$. Then $$\mathrm{CRC}_0\big(M(x) \cdot x^{NW} + g_K(x), v(x)\big) = \mathrm{CRC}_0\Big(g_K(x), \mathrm{CRC}_0\big(M(x), v(x)\big)\Big) = \Big(\mathrm{CRC}_0\big(M(x), v(x)\big) \cdot x^{NW} + g_K(x) \cdot x^D\Big) \bmod P(x) = \left(x^{NW}\sum_{n=0}^{N-1}v_{K,n}(x) \cdot x^{-nW} + x^D\sum_{n=0}^{N-1}m_{K,n}(x) \cdot x^{(N-1-n)W}\right) \bmod P(x) = \left(x^W\sum_{n=0}^{N-1}v_{K,n}(x) \cdot x^{(N-1-n)W} + x^D\sum_{n=0}^{N-1}m_{K,n}(x) \cdot x^{(N-1-n)W}\right) \bmod P(x)$$ $$= \sum_{n=0}^{N-1}\Big(v_{K,n}(x) \cdot x^W + m_{K,n}(x) \cdot x^D\Big) \cdot x^{(N-1-n)W} \bmod P(x) = \qquad (19)$$ $$= \sum_{n=0}^{N-1}\mathrm{CRC}_0\big(m_{K,n}(x), v_{K,n}(x)\big) \cdot x^{(N-1-n)W} \bmod P(x). \qquad (20)$$”
--
--   The $v_{K,n}$ are those of p. 18: “Once $v_{K,n}(x) = \mathrm{CRC}_0\big(M_n'(x), v_{0,n}(x)\big)$ are computed starting with $$v_{0,0} = v(x), \qquad v_{0,n} = 0, n \ge 1,$$”.
--
--   **Formalization note.** The statement says that the algorithm of §4.11 computes the CRC: the $v_{K,n}$ are the values the recurrence (16)–(17) produces (p. 18), not assumed equal to $\mathrm{CRC}_0(M_n', v_{0,n})$. In each display "$\bmod P(x)$" is read as applying to the whole sum. The message "$M(x) \cdot x^{NW} + g_K(x)$" is the concatenation $M g_K$ of the $K$ groups of $M$ and the group $g_K$. The identity holds for every $P$ of degree $D \ge 1$: the paper's derivation passes through the inverses of (18), which exist only when $x \nmid P$, but the conclusion uses none.
--
--   *Route.* p. 19, without inverses. The first step is (3) for $\mathrm{CRC}_0$. By (3) and the recurrence (16)–(17) (the milestone for (16)–(17)), $v_{K,n} = \mathrm{CRC}_0(M_n', v_{0,n})$. Then, instead of (18): by (14)–(15) multiplied through and $|M_n'| = |M|$, $\mathrm{CRC}_0(M, v)\,x^{(N-1)W} \equiv \sum_n v_{K,n}\,x^{(N-1-n)W} \pmod P$; multiply by $x^W$, which turns $x^{NW}\sum_n v_{K,n}x^{-nW}$ into $x^W\sum_n v_{K,n}x^{(N-1-n)W}$ as in the line before (19). (19) = (20) is definition (7) for the $W$-bit words $m_{K,n}$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 18–19, §4.11.2, eqs. (19)–(20)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc0_interleaved (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    crc0 P ((List.range (K + 1)).flatMap fun k => (List.range N).flatMap fun n => m k n) v =
        (∑ n ∈ Finset.range N, ((stripeCrc P W N m v K n * X ^ W + (m K n).poly * X ^ P.natDegree) *
          X ^ ((N - 1 - n) * W))) % P ∧
      crc0 P ((List.range (K + 1)).flatMap fun k => (List.range N).flatMap fun n => m k n) v =
        (∑ n ∈ Finset.range N, crc0 P (m K n) (stripeCrc P W N m v K n) * X ^ ((N - 1 - n) * W)) % P := by
  sorry

end KadatchJenkins
