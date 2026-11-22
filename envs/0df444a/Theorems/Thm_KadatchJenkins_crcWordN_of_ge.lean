-- Prove2me | Theorems.Thm_KadatchJenkins_crcWordN_of_ge
-- name    : KadatchJenkins.crcWordN_of_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-21T22:14:15.976177+00:00
-- url     : https://prove2.me/theorems/808ad971-d04e-4c49-a832-0ae329499078
-- title:
--   Eq. (21) — CrcWordN when D ≥ W
-- statement:
--   Let $P(x)$ be a polynomial over $\mathrm{GF}(2)$ of degree $D \ge 1$, $W \le D$ and $N \ge 0$. For all polynomials $v(x)$ of degree less than $D$ and $m(x)$ of degree less than $W$, let $v_H = \lfloor v/x^{D-W}\rfloor$ and $v_L = v \bmod x^{D-W}$. Then
--   1. $\deg v_H < W$, $\deg v_L < D - W$ and $v = v_L + v_H\,x^{D-W}$;
--   2. $\mathrm{CrcWordN}(m, v) = \Big((v_H + m)\,x^{(N-1)W+D} \bmod P\Big) + \Big((v_L\,x^W)\,x^{(N-1)W} \bmod P\Big)$ (eq. (21));
--   3. $(v_L\,x^W) \bmod P = v_L\,x^W$.
-- source:
--   Kadatch, A. and Jenkins, B., Everything we know about CRC but afraid to forget, September 3, 2010 (self-published white paper, distributed as doc/crc-doc.1.0.pdf with zlib 1.2.12 and later, and with Google's crcutil library; no DOI), p. 20, §4.11.3, eq. (21) (CrcWordN for D ≥ W)

import Mathlib
import Definitions.Def_KadatchJenkinsCrc

open Polynomial

namespace KadatchJenkins

theorem crcWordN_of_ge (P : (ZMod 2)[X]) (hP : 0 < P.natDegree) (W N : ℕ) (hWD : W ≤ P.natDegree)
    (m v : (ZMod 2)[X]) (hv : v.degree < (P.natDegree : WithBot ℕ)) (hm : m.degree < (W : WithBot ℕ)) :
    let vH := v /ₘ X ^ (P.natDegree - W)
    let vL := v %ₘ X ^ (P.natDegree - W)
    vH.degree < (W : WithBot ℕ) ∧ vL.degree < (((P.natDegree - W : ℕ)) : WithBot ℕ) ∧ v = vL + vH * X ^ (P.natDegree - W) ∧
      crcWordN P W N m v = ((vH + m) * X ^ ((N - 1) * W + P.natDegree)) % P +
        ((vL * X ^ W) * X ^ ((N - 1) * W)) % P ∧
      (vL * X ^ W) % P = vL * X ^ W := by
  sorry

end KadatchJenkins
