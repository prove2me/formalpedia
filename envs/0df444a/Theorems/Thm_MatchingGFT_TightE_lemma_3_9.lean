-- Prove2me | Theorems.Thm_MatchingGFT_TightE_lemma_3_9
-- name    : MatchingGFT.TightE.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:15.23986+00:00
-- url     : https://prove2.me/theorems/8e1fbc25-bd08-472d-92b0-282b65d40a84
-- title:
--   Lemma 3.9 — Exponential scale identity
-- statement:
--   For integrable $Q:(0,1)\to[0,\infty)$ and $t\in[0,1]$, with $h\sim\mathrm{Unif}(0,1)$, $\theta=e^{-h}$, $\eta=e^{-(1-h)}$: $E_h[\eta(h\int_0^{\theta t}Q+(1-h)\theta tQ(\theta t))]=\frac1e\int_0^tQ$. Monotonicity is not assumed.
--
--   Differences from the source:
--   - encoding: Q on (0,1); the integrand is defined to be zero at t = 0 → Q : ℝ → ℝ with hypotheses on (0,1); the product θt·Q(θt) is 0 at t = 0; reason: values outside (0,1) occur only on null sets, and the Lean product vanishes at t = 0
--   - encoding: E_h over h ∼ Unif(0,1) → the interval integral over h from 0 to 1; reason: same quantity
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Lemma 3.9, PDF p. 17

import Mathlib

open MeasureTheory Set

namespace MatchingGFT.TightE

/-- Lemma 3.9 (PDF p. 17): for integrable `Q : (0, 1) → [0, ∞)`, not assumed monotone, and `t ∈ [0, 1]`,
with `h ∼ Unif(0, 1)`, `θ = e^{-h}`, `η = e^{-(1-h)}`,
`E_h[η (h ∫₀^{θt} Q + (1 - h) θt Q(θt))] = (1/e) ∫₀^t Q`. At `t = 0` the product `θt Q(θt)` is `0`, which is the
source's convention that the integrand vanishes there. -/
theorem lemma_3_9 (Q : ℝ → ℝ) (hQ : ∀ u ∈ Ioo (0 : ℝ) 1, 0 ≤ Q u)
    (hint : IntegrableOn Q (Ioo 0 1)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ h in (0 : ℝ)..1, Real.exp (-(1 - h)) *
        (h * (∫ u in (0 : ℝ)..(Real.exp (-h) * t), Q u) +
          (1 - h) * ((Real.exp (-h) * t) * Q (Real.exp (-h) * t))) =
      (1 / Real.exp 1) * ∫ u in (0 : ℝ)..t, Q u := by sorry

end MatchingGFT.TightE
