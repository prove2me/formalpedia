-- Prove2me | Theorems.Thm_KadatchJenkins_crc_append
-- name    : KadatchJenkins.crc_append
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T21:57:42.772577+00:00
-- url     : https://prove2.me/theorems/2e39a0c0-51da-4900-a6ac-ba29639b2901
-- title:
--   Eq. (3) — Incremental CRC computation
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and $u(x)$ a polynomial of degree less than $D$. For all bit messages $M_1$, $M_2$ and every polynomial $v(x)$,
--   $$\mathrm{CRC}_u(M_1M_2, v) = \mathrm{CRC}_u\big(M_2, \mathrm{CRC}_u(M_1, v)\big),$$
--   where $M_1M_2$ is the concatenation and $\mathrm{CRC}_u(M, v) = \big((v - u)x^{|M|} + M(x)x^D + u\big) \bmod P$ is eq. (1).
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 4, §3.1, eq. (3) (Incremental CRC computation)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_append (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (M₁ M₂ : Message) (v : (ZMod 2)[X]) :
    crc P u (M₁ ++ M₂) v = crc P u M₂ (crc P u M₁ v) := by
  sorry

end KadatchJenkins
