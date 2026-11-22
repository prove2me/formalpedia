-- Prove2me | Theorems.Thm_KadatchJenkins_stripe_decomposition
-- name    : KadatchJenkins.stripe_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:12:48.198432+00:00
-- url     : https://prove2.me/theorems/01436fa0-93b4-432a-a18c-e6c6cbdd7ee0
-- title:
--   Eqs. (14)–(15) — The stripe decomposition
-- statement:
--   Let $W, K \ge 0$ and $N \ge 1$, and let $m_{k,n}$ ($0 \le k < K$, $0 \le n < N$) be $W$-bit words. Let $M = g_0g_1 \dots g_{K-1}$ with $g_k = m_{k,0} \dots m_{k,N-1}$, put
--   $$M_n(x) = \sum_{k=0}^{K-1}m_{k,n}(x)\,x^{(K-1-k)NW},$$
--   and let $M_n'$ be the message $m_{0,n}\,0^{(N-1)W}\,m_{1,n}\,0^{(N-1)W} \dots m_{K-1,n}\,0^{(N-1)W}$ (each word followed by $(N-1)W$ zero bits). Then
--   1. $M(x) = \sum_{n=0}^{N-1}M_n(x)\,x^{(N-1-n)W}$ (eq. (14));
--   2. for every $n$, $M_n'(x) = M_n(x)\,x^{(N-1)W}$ and $|M_n'| = KNW$;
--   3. $M(x)\,x^{(N-1)W} = \sum_{n=0}^{N-1}M_n'(x)\,x^{(N-1-n)W}$ (eq. (15), multiplied by $x^{(N-1)W}$).
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 16–17, §4.11.1, eqs. (14)–(15) (Interleaved word-by-word CRC computation)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem stripe_decomposition (W N K : ℕ) (hN : 0 < N) (m : ℕ → ℕ → Message) (hm : ∀ k n, (m k n).length = W) :
    let M : Message := (List.range K).flatMap fun k => (List.range N).flatMap fun n => m k n
    let Mn : ℕ → (ZMod 2)[X] := fun n =>
      ∑ k ∈ Finset.range K, (m k n).poly * X ^ ((K - 1 - k) * (N * W))
    let M' : ℕ → Message := fun n =>
      (List.range K).flatMap fun k => m k n ++ List.replicate ((N - 1) * W) 0
    M.poly = ∑ n ∈ Finset.range N, Mn n * X ^ ((N - 1 - n) * W) ∧
      (∀ n, (M' n).poly = Mn n * X ^ ((N - 1) * W) ∧ (M' n).length = K * (N * W)) ∧
      M.poly * X ^ ((N - 1) * W) = ∑ n ∈ Finset.range N, (M' n).poly * X ^ ((N - 1 - n) * W) := by
  sorry

end KadatchJenkins
