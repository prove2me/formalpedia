-- Prove2me | Theorems.Thm_KadatchJenkins_crc_append_forced
-- name    : KadatchJenkins.crc_append_forced
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:01:23.233822+00:00
-- url     : https://prove2.me/theorems/b6bf3c6b-40f0-4eac-b4ce-2ae369832c87
-- title:
--   §3.5 — Forcing a predefined CRC value
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $u(x)$ a polynomial of degree less than $D$, $P$ not divisible by $x$, and $W \ge D$. Then $x^W$ has an inverse modulo $P$: some $w(x)$ has $(w(x)x^W) \bmod P = 1$. For every such $w$, every bit message $M$, polynomial $v(x)$ and polynomial $R(x)$ of degree less than $D$, let $Q = \mathrm{CRC}_u(M, v)$ and
--   $$\hat q = \big((R - u)\,w - (Q - u)\big) \bmod P.$$
--   If $T$ is $M$ followed by the $D$ coefficients of $\hat q$ (from $x^{D-1}$ down to $x^0$) and then $W - D$ zero bits, then $\mathrm{CRC}_u(T, v) = R$. Moreover $\hat q$ is the only polynomial of degree less than $D$ with this property.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 6–7, §3.5 (Storing CRC value after the message), forcing a chosen CRC

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_append_forced (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree)
    (hu : u.degree < (P.natDegree : WithBot ℕ)) (hX : ¬ X ∣ P) (W : ℕ) (hW : P.natDegree ≤ W)
    (M : Message) (v R : (ZMod 2)[X]) (hR : R.degree < (P.natDegree : WithBot ℕ)) :
    (∃ w : (ZMod 2)[X], (w * X ^ W) % P = 1) ∧
      ∀ w : (ZMod 2)[X], (w * X ^ W) % P = 1 →
        let Q := crc P u M v
        let q := ((R - u) * w - (Q - u)) % P
        crc P u (M ++ Message.ofPoly P.natDegree q ++ List.replicate (W - P.natDegree) 0) v = R ∧
          ∀ t : (ZMod 2)[X], t.degree < (P.natDegree : WithBot ℕ) →
            crc P u (M ++ Message.ofPoly P.natDegree t ++ List.replicate (W - P.natDegree) 0) v = R → t = q := by
  sorry

end KadatchJenkins
