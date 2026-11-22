-- Prove2me | Theorems.Thm_KadatchJenkins_mulByXpowD_eq_crc0
-- name    : KadatchJenkins.mulByXpowD_eq_crc0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:12:14.491879+00:00
-- url     : https://prove2.me/theorems/2802c098-206c-416a-be73-d57614a1079f
-- title:
--   Eq. (11) — MulByXpowD as a simplified CRC
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$. For every bit message $V$,
--   $$\mathrm{MulByXpowD}\big(V(x)\big) = \mathrm{CRC}_0(V, 0),$$
--   where $\mathrm{MulByXpowD}(a) = (a\,x^D) \bmod P$ (eq. (10)) and $\mathrm{CRC}_0$ is eq. (7).
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 12, §4.8, eq. (11)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem mulByXpowD_eq_crc0 (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (V : Message) :
    mulByXpowD P V.poly = crc0 P V 0 := by
  sorry

end KadatchJenkins
