-- Prove2me | Theorems.Thm_KadatchJenkins_crc_change_init
-- name    : KadatchJenkins.crc_change_init
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T21:58:01.302454+00:00
-- url     : https://prove2.me/theorems/3e75e516-4f4b-4c1b-a132-87cac02edd8f
-- title:
--   Eq. (4) — Changing the initial CRC value
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and $u(x)$ a polynomial of degree less than $D$. For every bit message $M$ and all polynomials $v(x)$, $v'(x)$,
--   $$\mathrm{CRC}_u(M, v') = \mathrm{CRC}_u(M, v) + \big((v' - v)x^{|M|}\big) \bmod P.$$
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 4, §3.2, eq. (4) (Changing initial value)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_change_init (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (M : Message) (v v' : (ZMod 2)[X]) :
    crc P u M v' = crc P u M v + ((v' - v) * X ^ M.length) % P := by
  sorry

end KadatchJenkins
