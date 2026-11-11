-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_5_7
-- name    : OrderSelProphet.Kernel.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:58:04.105636+00:00
-- url     : https://prove2.me/theorems/996934e2-baff-4196-9405-6684c42a08a5
-- title:
--   Lemma 5.7 — threshold lag for $K_0$: $a_\lambda(u_r)-A_\lambda(x_\lambda(u_r))=e^{-r}(e^{h(r)}-1-h(r))\ge0$ and $1-Y(r)\le(1+h(r))e^{-r}$
-- statement:
--   Let $\lambda\in\Lambda$, $h(r)=h_\lambda(u_r)$ and $Y(r)=y_{K_0,\lambda}(t_r)$ in exponential coordinates. For every $r\ge0$,
--   $$a_\lambda(u_r)-A_\lambda\big(x_\lambda(u_r)\big)=e^{-r}\big(e^{h(r)}-1-h(r)\big)\ge0,\quad(56)$$
--   and consequently
--   $$1-Y(r)\le\big(1+h(r)\big)e^{-r}.\quad(57)$$
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: Y(r) = y(t_r) with y = y_{K0,λ} (Lemma 5.6); h(r) = h_λ(u_r) (51) → yK K0 λ (tR r) and hExp λ r = hP λ (uA r); reason: the paper's definitions in exponential coordinates
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma 5.7, p. 25

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Coordinates

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma 5.7 (Threshold lag), p. 25, for the kernel `K0`, with `Y(r) = y_{K0,λ}(t_r)` and
`h(r) = h_λ(u_r)`. -/
theorem lemma_5_7 (lam : Profile) (r : ℝ) (hr : 0 ≤ r) :
    linArea lam.1 (uA r) - areaP lam.1 (xP lam.1 (uA r)) =
        Real.exp (-r) * (Real.exp (hExp lam.1 r) - 1 - hExp lam.1 r) ∧
      0 ≤ Real.exp (-r) * (Real.exp (hExp lam.1 r) - 1 - hExp lam.1 r) ∧
      1 - yK K0 lam.1 (tR r) ≤ (1 + hExp lam.1 r) * Real.exp (-r) := by sorry

end OrderSelProphet.Kernel
