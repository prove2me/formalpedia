-- Prove2me | Theorems.Thm_OnDemandRideHailing_CallNoCall_section_5_1_expected_en_route_time
-- name    : OnDemandRideHailing.CallNoCall.section_5_1_expected_en_route_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:34.586255+00:00
-- url     : https://prove2.me/theorems/56cb18b8-e9f2-4d94-8a2b-52f62e6e7309
-- title:
--   Expected en route time to the nearest of $m$ uniformly placed taxis: $\int_0^{R/v}((R-vt)/R)^m\,dt=R/(v(m+1))$
-- statement:
--   Let $R>0$ be the perimeter of the road and $v>0$ the taxis' speed. For every natural number $m$,
--
--   $$
--   \int_0^{R/v}\left(\frac{R-vt}{R}\right)^{m}dt=\frac{R}{v(m+1)} .
--   $$
--
--   With $m=k-n$ idle taxis placed uniformly on the road, $((R-vt)/R)^{k-n}$ is the probability that the en route time to the nearest one is at least $t$, and the identity gives the expected en route time $R/(v(k-n+1))$ of the call approximation (1). For other exponents the same identity turns the exponential-free parts of the no-call integrals (3) into the en route terms of (1).
--
--   Differences from the source:
--
--   - generalization: the exponent k − n (k − n idle taxis, n < k) → every exponent m : ℕ; reason: the integral identity holds for every m and specializes to the printed case m = k − n
--   - reading: §3's R the perimeter of the road and v the taxis' speed (pp. 7–8) → hypotheses 0 < R, 0 < v; reason: standing assumptions of the model; they exclude only parameter values that are not the model
-- source:
--   Feng, Kong, Wang, We Are on the Way: Analysis of On-Demand Ride-Hailing Systems, SSRN 2960991, §5.1, unnumbered computation, p. 15

import Mathlib

namespace OnDemandRideHailing.CallNoCall

/-- **The expected en route time to the nearest of `m` uniformly placed taxis.**
Feng, Kong, Wang, *We Are on the Way: Analysis of On-Demand Ride-Hailing Systems*, SSRN 2960991, §5.1, unnumbered computation, p. 15:
`P(t(1c)_e ≥ t) = Π_{i=1}^{k−n} P(li/v ≥ t) = ((R − vt)/R)^{k−n}`, and thus the expected en route
time `t̄(1c)_e = E[t(1c)_e] = ∫_0^{R/v} P(t(1c)_e ≥ t) dt = R/(v(k−n+1))`.

For a road of perimeter `R > 0`, speed `v > 0` and every natural number `m`,
`∫_0^{R/v} ((R − vt)/R)^m dt = R/(v(m+1))`.

**Formalization Note.** Stated for every exponent `m`, not only `m = k − n`; the paper's case is
`m = k − n`. With `m = n − k` and `m = 1` the same identity turns the exponential-free part of
the no-call integrals (3) into the en route terms of (1). -/
theorem section_5_1_expected_en_route_time {R v : ℝ} (hR : 0 < R) (hv : 0 < v) (m : ℕ) :
    ∫ t in (0 : ℝ)..R / v, ((R - v * t) / R) ^ m = R / (v * ((m : ℝ) + 1)) := by sorry

end OnDemandRideHailing.CallNoCall
