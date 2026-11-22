-- Prove2me | Theorems.Thm_KadatchJenkins_crc0_eq_sum_stripeCrc_mul_inv
-- name    : KadatchJenkins.crc0_eq_sum_stripeCrc_mul_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:13:22.551594+00:00
-- url     : https://prove2.me/theorems/eb520c67-9cc8-493d-96ee-5d6aeabb4fcb
-- title:
--   Eq. (18) — Combining the stripe CRCs with inverses
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $W \ge 0$, $N \ge 1$ and $K \ge 0$. An inverse of $x^W$ modulo $P$, a $w(x)$ with $(w\,x^W) \bmod P = 1$, exists if and only if $x \nmid P$ or $W = 0$. Let $m_{k,n}$ be $W$-bit words, $M$ the message $m_{0,0} \dots m_{0,N-1}\,m_{1,0} \dots m_{K-1,N-1}$ ($K$ groups of $N$ words), $v(x)$ a polynomial, and $v_{k,n}$ the stripe CRCs ($v_{0,0} = v$, $v_{0,n} = 0$ for $n \ge 1$, $v_{k+1,n} = \mathrm{CrcWordN}(m_{k,n}, v_{k,n})$). Then for every such inverse $w$,
--   $$\mathrm{CRC}_0(M, v) = \Big(\sum_{n=0}^{N-1}v_{K,n}\,w^n\Big) \bmod P.$$
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 18, §4.11.2, eq. (18)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc0_eq_sum_stripeCrc_mul_inv (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ)
    (hN : 0 < N) (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    ((∃ w : (ZMod 2)[X], (w * X ^ W) % P = 1) ↔ (¬ X ∣ P ∨ W = 0)) ∧
      ∀ w : (ZMod 2)[X], (w * X ^ W) % P = 1 →
        crc0 P ((List.range K).flatMap fun k => (List.range N).flatMap fun n => m k n) v =
          (∑ n ∈ Finset.range N, stripeCrc P W N m v K n * w ^ n) % P := by
  sorry

end KadatchJenkins
