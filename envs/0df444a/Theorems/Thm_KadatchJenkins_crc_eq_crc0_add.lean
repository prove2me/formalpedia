-- Prove2me | Theorems.Thm_KadatchJenkins_crc_eq_crc0_add
-- name    : KadatchJenkins.crc_eq_crc0_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:05:00.969713+00:00
-- url     : https://prove2.me/theorems/13643547-64ea-4fb9-9e80-bb668c02e84f
-- title:
--   §4.5 — CRC from the simplified CRC
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $u(x)$ a polynomial of degree less than $D$, and $\mathrm{CRC}_0(M, v) = \big(v\,x^{|M|} + M(x)x^D\big) \bmod P$ (eq. (7)). For every polynomial $v(x)$:
--   1. $\mathrm{CRC}_u(M, v) = \mathrm{CRC}_0(M, v - u) + u$ for every bit message $M$;
--   2. for every nonempty list of messages $M_1, \dots, M_K$ ($K \ge 1$), with $v_0 = v - u$ and $v_k = \mathrm{CRC}_0(M_k, v_{k-1})$, the CRC of the concatenation $M = M_1 \dots M_K$ is $\mathrm{CRC}_u(M, v) = v_K + u$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 9, §4.5, eq. (7) (Simplified CRC computation)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_eq_crc0_add (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (v : (ZMod 2)[X]) :
    (∀ M : Message, crc P u M v = crc0 P M (v - u) + u) ∧
      ∀ Ms : List Message, Ms ≠ [] → crc P u Ms.flatten v = Ms.foldl (fun w Mk => crc0 P Mk w) (v - u) + u := by
  sorry

end KadatchJenkins
