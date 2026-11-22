-- Prove2me | Theorems.Thm_KadatchJenkins_stripeCrc_eq_crc0
-- name    : KadatchJenkins.stripeCrc_eq_crc0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:13:04.861348+00:00
-- url     : https://prove2.me/theorems/6f436a61-3c30-4b69-b7be-c32335b40c87
-- title:
--   Eqs. (16)–(17) — The per-stripe recurrence
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $W \ge 0$, $N \ge 1$, $m_{k,n}$ ($k \ge 0$, $0 \le n < N$) $W$-bit words and $v(x)$ a polynomial. Let $v_{0,0} = v$, $v_{0,n} = 0$ for $n \ge 1$, and $v_{k+1,n} = \mathrm{CrcWordN}(m_{k,n}, v_{k,n})$, where $\mathrm{CrcWordN}(m, v) = \big((v\,x^W + m(x)\,x^D)\,x^{(N-1)W}\big) \bmod P$. Then
--   1. for all $k$, $n$: $\mathrm{CRC}_0\big(m_{k,n}\,0^{(N-1)W},\ v_{k,n}\big) = \mathrm{CrcWordN}(m_{k,n}, v_{k,n})$, where $m_{k,n}\,0^{(N-1)W}$ is the word followed by $(N-1)W$ zero bits (eqs. (16)–(17));
--   2. for all $K \ge 1$ and all $n$: $v_{K,n} = \mathrm{CRC}_0\big(M_n', v_{0,n}\big)$, where $M_n' = m_{0,n}\,0^{(N-1)W} \dots m_{K-1,n}\,0^{(N-1)W}$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 17–18, §4.11.1, eqs. (16)–(17)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem stripeCrc_eq_crc0 (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hN : 0 < N)
    (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) (v : (ZMod 2)[X]) :
    (∀ k n, crc0 P (m k n ++ List.replicate ((N - 1) * W) 0) (stripeCrc P W N m v k n) =
        crcWordN P W N (m k n).poly (stripeCrc P W N m v k n)) ∧
      ∀ K n, 0 < K → stripeCrc P W N m v K n =
        crc0 P ((List.range K).flatMap fun k => m k n ++ List.replicate ((N - 1) * W) 0)
          (stripeCrc P W N m v 0 n) := by
  sorry

end KadatchJenkins
