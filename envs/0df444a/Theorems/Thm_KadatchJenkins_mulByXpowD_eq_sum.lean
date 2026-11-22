-- Prove2me | Theorems.Thm_KadatchJenkins_mulByXpowD_eq_sum
-- name    : KadatchJenkins.mulByXpowD_eq_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:12:30.397012+00:00
-- url     : https://prove2.me/theorems/4db3bf96-643b-4d2b-83a6-2748657b2116
-- title:
--   Eqs. (12)–(13) — Word-by-word CRC by slicing
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, let $W \ge 0$ and $B \ge 1$, and let $v(x)$ be a polynomial of degree less than $W$. Put $K = \lceil W/B\rceil$ and $v_k = \big\lfloor v / x^{(K-1-k)B}\big\rfloor \bmod x^B$ for $0 \le k < K$. Then
--   $$v = \sum_{k=0}^{K-1}v_k\,x^{(K-1-k)B} \qquad\text{and}\qquad \mathrm{MulByXpowD}(v) = \sum_{k=0}^{K-1}\Big(v_k\,x^{(K-1-k)B+D} \bmod P\Big).$$
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 12–13, §4.9, eqs. (12)–(13) (Word-by-word CRC computation)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem mulByXpowD_eq_sum (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W B : ℕ) (hB : 0 < B)
    (v : (ZMod 2)[X]) (hv : v.degree < (W : WithBot ℕ)) :
    let K := (W + B - 1) / B
    let vk : ℕ → (ZMod 2)[X] := fun k => (v /ₘ X ^ ((K - 1 - k) * B)) %ₘ X ^ B
    v = ∑ k ∈ Finset.range K, vk k * X ^ ((K - 1 - k) * B) ∧
      mulByXpowD P v = ∑ k ∈ Finset.range K, (vk k * X ^ ((K - 1 - k) * B + P.natDegree)) % P := by
  sorry

end KadatchJenkins
