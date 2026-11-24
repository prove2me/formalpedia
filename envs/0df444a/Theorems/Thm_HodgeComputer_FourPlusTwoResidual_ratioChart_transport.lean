-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_ratioChart_transport
-- name    : HodgeComputer.FourPlusTwoResidual.ratioChart_transport
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-24T07:29:33.831637+00:00
-- url     : https://prove2.me/theorems/581cbc62-1f49-4551-8677-4aac2c5eb525
-- title:
--   Transport of a ratio-chart rational current with source t^4 to the four-variable core equation
-- statement:
--   In the ratio coordinates $(a, b, c, d) = (a, a r, a t, a s t)$ with $H = a^6 P(r, s, t)$ and $a, t \neq 0$, if a three-component chart current $(q_r, q_s, q_t)$ satisfies
--
--   $$
--   \frac{2}{3}\bigl(q_r D_r P + q_s D_s P + q_t D_t P\bigr) - P\bigl(D_r q_r + D_s q_s + D_t q_t\bigr) = t^4,
--   $$
--
--   then setting $(p_a, p_b, p_c, p_d) = \frac{2 a}{3 t}(0,\; q_r,\; q_t,\; s q_t + t q_s)$ satisfies the physical four-variable twisted divergence identity $p(H) - \frac{3}{2} H \operatorname{div}(p) = a^6 t^3 = a^3 c^3$.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

theorem HodgeComputer.FourPlusTwoResidual.ratioChart_transport :
    ∀ {K : Type} [Field K] [CharZero K]
      (Dr Ds Dt : Derivation ℤ K K)
      (a s t P qr qs qt : K),
      a ≠ 0 → t ≠ 0 →
      Dr a = 0 → Ds a = 0 → Dt a = 0 →
      Dr t = 0 → Ds t = 0 → Dt t = 1 →
      Ds s = 1 →
      -(P * (Dr qr + Ds qs + Dt qt) -
          (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P)) = t ^ 4 →
      let H := a ^ 6 * P
      let db := fun z : K => Dr z / a
      let dc := fun z : K => (Dt z - s / t * Ds z) / a
      let dd := fun z : K => Ds z / (a * t)
      let pb := (2 : K) * a * qr / (3 * t)
      let pc := (2 : K) * a * qt / (3 * t)
      let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
      pb * db H + pc * dc H + pd * dd H -
        (3 / 2 : K) * H * (db pb + dc pc + dd pd) = a ^ 6 * t ^ 3 := by sorry
