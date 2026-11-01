-- Prove2me | Theorems.Thm_ObsArrivalPricing_proposition_3
-- name    : ObsArrivalPricing.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:43:47.41459+00:00
-- url     : https://prove2.me/theorems/0c939336-f7b6-4e14-af90-11670ef0cebe
-- title:
--   Proposition 3 — under a uniform random shift the arrival's phase is uniform
-- statement:
--   Let $T>0$, fix an arrival time $\tau\in\mathbb R$, and let $t_0\sim\mathrm{Unif}[0,2T]$. Under the shifted policy $\hat p_{t_0}(t)=\hat p(t+t_0)$ the buyer arriving at $\tau$ sees the phase $s=\tau+t_0 \bmod 2T\in(0,2T]$. Then $s\sim\mathrm{Unif}(0,2T]$: the image of Lebesgue measure on $[0,2T]$ under $t_0\mapsto(\tau+t_0\bmod 2T)$ is Lebesgue measure on $(0,2T]$,
--   $$\mathrm{Leb}|_{[0,2T]}\circ\big(t_0\mapsto \tau+t_0 \bmod 2T\big)^{-1}=\mathrm{Leb}|_{(0,2T]}.$$
--
--   Because the arrival time and the shift are independent, the buyer's arrival, conditional on the period in which it falls, is uniform within that period, whatever the arrival distribution $G$. This removes $G$ from the analysis of $\hat p$.
--
--   Differences from the source:
--   - reading: "the buyer's arrival, conditional in the arrival interval, is Unif[0,2T]" → for every fixed arrival $\tau$ the phase of $\tau+t_0$ is uniform on $(0,2T]$; reason: the proof (p.A6) and its use on p.A8 fix $\tau$; with $\tau$ independent of $t_0$ this gives the printed conditional law
--   - encoding: uniform laws on $[0,2T]$ → Lebesgue measure restricted to $[0,2T]$ and to $(0,2T]$, both unnormalized; reason: both sides carry the same factor $1/(2T)$
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), Proposition 3, p.20; proof p.A6; use in the proof of Lemma 3, p.A8 ("fix the buyer arrival time τ")

import Mathlib
import Definitions.Def_ObsArrivalPricing_PeriodicPolicy

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- Proposition 3 (SSRN 3541494, p.20; proof p.A6), per fixed arrival time. For `T > 0`, a fixed
arrival time `τ` and a uniform shift `t0 ∼ Unif[0, 2T]`, the phase of the arrival under
`p̂_{t0}(t) = p̂(t + t0)`, i.e. the position of `τ + t0` in its period, is uniform on `(0, 2T]`:
the push-forward of Lebesgue measure on `[0, 2T]` is Lebesgue measure on `(0, 2T]`. -/
theorem proposition_3 {T : ℝ} (hT : 0 < T) (τ : ℝ) :
    (volume.restrict (Icc 0 (2 * T))).map (fun t0 => phase T (τ + t0)) =
      volume.restrict (Ioc 0 (2 * T)) := by sorry

end ObsArrivalPricing
