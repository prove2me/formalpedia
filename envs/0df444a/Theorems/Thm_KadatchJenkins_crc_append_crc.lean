-- Prove2me | Theorems.Thm_KadatchJenkins_crc_append_crc
-- name    : KadatchJenkins.crc_append_crc
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:01:04.669293+00:00
-- url     : https://prove2.me/theorems/437eea8d-bf6e-48e6-aa06-60625b8ed6ef
-- title:
--   §3.5 — The CRC of a message followed by its CRC
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $u(x)$ a polynomial of degree less than $D$, and $W \ge D$. For every bit message $M$ and polynomial $v(x)$, let $Q = \mathrm{CRC}_u(M, v)$, and let $T$ be $M$ followed by the $D$ coefficients of $Q$ (from $x^{D-1}$ down to $x^0$) and then $W - D$ zero bits. Then $T(x) = M(x)\,x^W + Q(x)\,x^{W-D}$ and
--   $$\mathrm{CRC}_u(T, v) = \big(u(x)(1 - x^W)\big) \bmod P,$$
--   a value that depends on neither $M$ nor $v$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 6, §3.5 (Storing CRC value after the message)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_append_crc (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (W : ℕ) (hW : P.natDegree ≤ W) (M : Message) (v : (ZMod 2)[X]) :
    (M ++ Message.ofPoly P.natDegree (crc P u M v) ++ List.replicate (W - P.natDegree) 0).poly =
        M.poly * X ^ W + crc P u M v * X ^ (W - P.natDegree) ∧
      crc P u (M ++ Message.ofPoly P.natDegree (crc P u M v) ++ List.replicate (W - P.natDegree) 0) v =
        (u * (1 - X ^ W)) % P := by
  sorry

end KadatchJenkins
