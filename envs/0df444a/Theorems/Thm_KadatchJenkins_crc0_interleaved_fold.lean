-- Prove2me | Theorems.Thm_KadatchJenkins_crc0_interleaved_fold
-- name    : KadatchJenkins.crc0_interleaved_fold
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:13:42.754171+00:00
-- url     : https://prove2.me/theorems/bc14f6b4-c7ad-454a-996d-2f75a2276125
-- title:
--   §4.11.2 — Computing the combination (20) by a fold
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $W \ge 0$, $N \ge 1$, $K \ge 0$, $m_{k,n}$ $W$-bit words, $v(x)$ a polynomial, and $v_{k,n}$ the stripe CRCs ($v_{0,0} = v$, $v_{0,n} = 0$ for $n \ge 1$, $v_{k+1,n} = \mathrm{CrcWordN}(m_{k,n}, v_{k,n})$). Let $v_0' = 0$ and $v_{n+1}' = \mathrm{CRC}_0(m_{K,n}, v_n' + v_{K,n})$ for $n = 0, \dots, N-1$. Then
--   $$v_N' = \Big(\sum_{n=0}^{N-1}\mathrm{CRC}_0(m_{K,n}, v_{K,n})\,x^{(N-1-n)W}\Big) \bmod P,$$
--   the right-hand side of (20).
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 19, §4.11.2, the implementation of (20)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc0_interleaved_fold (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N K : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    (List.range N).foldl (fun v' n => crc0 P (m K n) (v' + stripeCrc P W N m v K n)) 0 =
      (∑ n ∈ Finset.range N, crc0 P (m K n) (stripeCrc P W N m v K n) * X ^ ((N - 1 - n) * W)) % P := by
  sorry

end KadatchJenkins
