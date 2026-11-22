-- Prove2me | Theorems.Thm_KadatchJenkins_crc_replace
-- name    : KadatchJenkins.crc_replace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T21:59:21.884791+00:00
-- url     : https://prove2.me/theorems/d350e260-75fe-4c86-87f8-9020445a41b6
-- title:
--   §3.4 — In-place modification of a CRC-ed message
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and $u(x)$ a polynomial of degree less than $D$. Let $A$, $B$, $B'$, $C$ be bit messages with $|B'| = |B|$, let $M = ABC$ and $M' = AB'C$, and let $v(x)$ be any polynomial. Then
--   1. $\mathrm{CRC}_u(M', v) = \mathrm{CRC}_u(M, v) + \big((B'(x) - B(x))x^{|C| + D}\big) \bmod P$;
--   2. $\mathrm{CRC}_u(B', v) - \mathrm{CRC}_u(B, v) = \big((B'(x) - B(x))x^D\big) \bmod P$;
--   3. $\mathrm{CRC}_u(M', v) = \mathrm{CRC}_u(M, v) + \Delta$, where $\Delta = \Big(\big(\mathrm{CRC}_u(B', v) - \mathrm{CRC}_u(B, v)\big)x^{|C|}\Big) \bmod P$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), pp. 5–6, §3.4 (In-place modification of CRC-ed message)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_replace (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree) (hu : u.degree < (P.natDegree : WithBot ℕ))
    (A B B' Cm : Message) (hB : B'.length = B.length) (v : (ZMod 2)[X]) :
    crc P u (A ++ B' ++ Cm) v =
        crc P u (A ++ B ++ Cm) v + ((B'.poly - B.poly) * X ^ (Cm.length + P.natDegree)) % P ∧
      crc P u B' v - crc P u B v = ((B'.poly - B.poly) * X ^ P.natDegree) % P ∧
      crc P u (A ++ B' ++ Cm) v =
        crc P u (A ++ B ++ Cm) v + ((crc P u B' v - crc P u B v) * X ^ Cm.length) % P := by
  sorry

end KadatchJenkins
