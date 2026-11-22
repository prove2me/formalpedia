-- Prove2me | Theorems.Thm_KadatchJenkins_crc_append_of_crcs
-- name    : KadatchJenkins.crc_append_of_crcs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T21:58:18.687849+00:00
-- url     : https://prove2.me/theorems/5062920c-2149-4612-a8a1-cc830d32b8ca
-- title:
--   §3.3 — Concatenation of CRCs
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, and $u(x)$ a polynomial of degree less than $D$. For all bit messages $M_1$, $M_2$ and all polynomials $v$, $v_1$, $v_2$, put
--   $$v_1' = \mathrm{CRC}_u(M_1, v_1) + \big((v - v_1)x^{|M_1|}\big) \bmod P, \qquad v_2' = \mathrm{CRC}_u(M_2, v_2) + \big((v_1' - v_2)x^{|M_2|}\big) \bmod P.$$
--   Then $v_1' = \mathrm{CRC}_u(M_1, v)$, $v_2' = \mathrm{CRC}_u(M_2, v_1')$, and $\mathrm{CRC}_u(M_1M_2, v) = v_2'$.
--
--   That is: $v_1'$ and $v_2'$ are computed from the known $\mathrm{CRC}_u(M_1, v_1)$ and $\mathrm{CRC}_u(M_2, v_2)$ by formula (4), they are the values steps 1 and 2 claim, and $v_2'$ is the CRC of the concatenation.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 5, §3.3 (Concatenation of CRCs)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc_append_of_crcs (P u : (ZMod 2)[X]) (hP : 0 < P.natDegree)
    (hu : u.degree < (P.natDegree : WithBot ℕ)) (M₁ M₂ : Message) (v v₁ v₂ : (ZMod 2)[X]) :
    let v₁' := crc P u M₁ v₁ + ((v - v₁) * X ^ M₁.length) % P
    let v₂' := crc P u M₂ v₂ + ((v₁' - v₂) * X ^ M₂.length) % P
    v₁' = crc P u M₁ v ∧ v₂' = crc P u M₂ v₁' ∧ crc P u (M₁ ++ M₂) v = v₂' := by
  sorry

end KadatchJenkins
