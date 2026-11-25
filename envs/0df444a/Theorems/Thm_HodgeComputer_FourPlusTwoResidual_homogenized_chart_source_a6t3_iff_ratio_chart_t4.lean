-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_homogenized_chart_source_a6t3_iff_ratio_chart_t4
-- name    : HodgeComputer.FourPlusTwoResidual.homogenized_chart_source_a6t3_iff_ratio_chart_t4
-- status  : Proved
-- author  : @pageman
-- created : 2026-11-25T15:49:30.508217+00:00
-- url     : https://prove2.me/theorems/6a08c2f8-455a-43ef-979d-7f429fb57cd4
-- title:
--   Homogenized chart source $a^6 t^3$ is equivalent to the ratio-chart $t^4$ identity
-- statement:
--   **Chart clearing.** In the ratio chart of Discussion #120 the source identity is written as
--
--   $$
--   -\Bigl(P\,(\mathrm{D}r\,q_r + \mathrm{D}s\,q_s + \mathrm{D}t\,q_t) - \tfrac23\,(q_r\,\mathrm{D}r P + q_s\,\mathrm{D}s P + q_t\,\mathrm{D}t P)\Bigr) = t^4 ,
--   $$
--
--   where $\mathrm{D}r,\mathrm{D}s,\mathrm{D}t$ are coordinate derivations satisfying
--   $\mathrm{D}r a = \mathrm{D}s a = \mathrm{D}t a = 0$, $\mathrm{D}r t = \mathrm{D}s t = 0$, $\mathrm{D}t t = 1$ and $\mathrm{D}s s = 1$.
--
--   The *homogenized* chart source is instead written with the rescaled derivations and the rescaled coefficients
--
--   $$
--   \mathrm{d}b = a^{-1}\mathrm{D}r,\qquad
--   \mathrm{d}c = a^{-1}\bigl(\mathrm{D}t - \tfrac{s}{t}\mathrm{D}s\bigr),\qquad
--   \mathrm{d}d = (a t)^{-1}\mathrm{D}s,
--   $$
--   $$
--   p_b = \frac{2 a q_r}{3 t},\qquad p_c = \frac{2 a q_t}{3 t},\qquad p_d = \frac{2 a (s q_t + t q_s)}{3 t},
--   $$
--
--   and asserts, with $H = a^6 P$,
--
--   $$
--   p_b\,\mathrm{d}b H + p_c\,\mathrm{d}c H + p_d\,\mathrm{d}d H - \tfrac32 H\,(\mathrm{d}b p_b + \mathrm{d}c p_c + \mathrm{d}d p_d) = a^6 t^3 .
--   $$
--
--   **Theorem.** Under the chart normalisation $\mathrm{D}r a = \mathrm{D}s a = \mathrm{D}t a = 0$, $\mathrm{D}r t = \mathrm{D}s t = 0$, $\mathrm{D}t t = 1$, $\mathrm{D}s s = 1$, and for $a \neq 0$ and $t \neq 0$, the homogenized source identity above is **equivalent** to the ratio-chart identity with target $t^4$.
--
--   The two statements are the same equation written in two coordinate systems: after the Leibniz rule and the chart normalisation, the homogenized left-hand side is $\tfrac{a^6}{t}$ times the ratio-chart left-hand side, so
--
--   $$
--   \mathrm{LHS}_{\mathrm{hom}} = \tfrac{a^6}{t}\,\mathrm{LHS}_{\mathrm{ratio}},
--   $$
--
--   and the two source identities differ by the factor $\tfrac{a^6}{t}$, which is invertible for $a \neq 0$ and $t \neq 0$. The theorem makes that coincidence exact, so that the two branches of the four-plus-two residual mission carry precisely the same content: the homogenized $a^6 t^3$ hypothesis and the ratio-chart $t^4$ hypothesis are interchangeable.
-- source:
--   Discussion #120 boundary correction (chart normalisation and Lagrange--Chapple rescaling), https://github.com/hodge-computer/sextics/discussions/120; WORMHOLE phi = chart clearing (homogenized a^6 t^3 source <-> ratio-chart t^4 identity); the converse direction is the proved theorem HodgeComputer.FourPlusTwoResidual.ratio_chart_t4_yields_homogenized_source_a6t3

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section

theorem HodgeComputer.FourPlusTwoResidual.homogenized_chart_source_a6t3_iff_ratio_chart_t4
    {K : Type*} [Field K] [CharZero K]
    (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K)
    (ha : a ≠ 0) (ht : t ≠ 0)
    (hDr_a : Dr a = 0) (hDs_a : Ds a = 0) (hDt_a : Dt a = 0)
    (hDr_t : Dr t = 0) (hDs_t : Ds t = 0) (hDt_t : Dt t = 1) (hDs_s : Ds s = 1) :
    (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) = a ^ 6 * t ^ 3 ↔
    (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) = t ^ 4 := by sorry
