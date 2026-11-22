-- Prove2me | Theorems.Thm_KadatchJenkins_crc_roll
-- name    : KadatchJenkins.crc_roll
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-21T22:09:43.68986+00:00
-- url     : https://prove2.me/theorems/5a8d10ea-68e3-4632-b48c-ed5e0117ba2d
-- title:
--   §4.7 — Rolling CRC
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and $u(x)$ a polynomial of degree less than $D$. Let $m_0, m_1, \dots$ be $W$-bit symbols, $N \ge 0$, $v(x)$ any polynomial, and $M_j = m_j m_{j+1} \dots m_{j+N-1}$, with $C_j = \mathrm{CRC}_u(M_j, v)$. For every $k$, put
--   $$F = \big(C_k\,x^W + m_{k+N}(x)\,x^D\big) \bmod P, \qquad G = \Big(\big((v - u)x^{NW} + u\big)(1 - x^W) - m_k(x)\,x^{D+NW}\Big) \bmod P.$$
--   Then
--   1. $M_{k+1}(x) = M_k(x)\,x^W - m_k(x)\,x^{NW} + m_{k+N}(x)$;
--   2. $C_{k+1} = \Big((v - u)x^{NW} + u + \sum_{n=0}^{N-1}m_{k+1+n}(x)\,x^{D+W(N-1-n)}\Big) \bmod P$;
--   3. $C_{k+1} = F + G$;
--   4. $\deg F < D$ and $\deg G < D$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 11–12, §4.7 (Rolling CRC)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_roll (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (W N : ℕ) (m : ℕ → Message) (hm : ∀ k, (m k).length = W) (v : (ZMod 2)[X]) (k : ℕ) :
    let Msg : ℕ → Message := fun j => (List.range N).flatMap fun n => m (j + n)
    let F := (crc P u (Msg k) v * X ^ W + (m (k + N)).poly * X ^ P.natDegree) % P
    let G := (((v - u) * X ^ (N * W) + u) * (1 - X ^ W) -
      (m k).poly * X ^ (P.natDegree + N * W)) % P
    (Msg (k + 1)).poly = (Msg k).poly * X ^ W - (m k).poly * X ^ (N * W) + (m (k + N)).poly ∧
    crc P u (Msg (k + 1)) v = ((v - u) * X ^ (N * W) + u +
        ∑ n ∈ Finset.range N, (m (k + 1 + n)).poly * X ^ (P.natDegree + W * (N - 1 - n))) % P ∧
      crc P u (Msg (k + 1)) v = F + G ∧ F.degree < (P.natDegree : WithBot ℕ) ∧ G.degree < (P.natDegree : WithBot ℕ) := by
  sorry

end KadatchJenkins
