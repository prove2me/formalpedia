-- Prove2me | Theorems.Thm_KadatchJenkins_crc0_word_of_ge
-- name    : KadatchJenkins.crc0_word_of_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:09:26.864065+00:00
-- url     : https://prove2.me/theorems/a1e0b654-d432-45f4-a2d9-2368e105df41
-- title:
--   Eq. (9) — Byte-by-byte CRC when D ≥ W
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$ and $W \le D$. For every $W$-bit message $M$ and every polynomial $v(x)$ of degree less than $D$, let $v_H = \lfloor v / x^{D-W}\rfloor$ and $v_L = v \bmod x^{D-W}$. Then
--   1. $v = v_L + v_H\,x^{D-W}$, $\deg v_H < W$ and $\deg v_L < D - W$;
--   2. $(v_L\,x^W) \bmod P = v_L\,x^W$;
--   3. $\mathrm{CRC}_0(M, v) = v_L\,x^W + \mathrm{MulByXpowD}\big(v_H + M(x)\big)$, where $\mathrm{MulByXpowD}(a) = (a\,x^D) \bmod P$ (eq. (10)).
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 10, §4.6, eq. (9) (Byte-by-byte CRC computation, D ≥ W)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crc0_word_of_ge (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W : ℕ) (hWD : W ≤ P.natDegree)
    (M : Message) (hM : M.length = W) (v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) :
    let vH := v /ₘ X ^ (P.natDegree - W)
    let vL := v %ₘ X ^ (P.natDegree - W)
    v = vL + vH * X ^ (P.natDegree - W) ∧ vH.degree < (W : WithBot ℕ) ∧ vL.degree < (((P.natDegree - W : ℕ)) : WithBot ℕ) ∧
      (vL * X ^ W) % P = vL * X ^ W ∧
      crc0 P M v = vL * X ^ W + mulByXpowD P (vH + M.poly) := by
  sorry

end KadatchJenkins
