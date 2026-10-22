-- Prove2me | Theorems.Thm_LogMeanVar_Complete_c2_spike_decomposition
-- name    : LogMeanVar.Complete.c2_spike_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:53.318007+00:00
-- url     : https://prove2.me/theorems/bbeb31aa-65cc-4f17-b9d0-0a480ba1c9ce
-- title:
--   Proof of Theorem 2 (App. C.2), p. O–11 — J(π^{h,v}) = J(π̂) + ∫_t^{t+h}([v(µ−r) − (1+γ)/2 v²σ²] − [π̂_s(µ−r) − (1+γ)/2 π̂_s²σ²]) ds
-- statement:
--   In the complete market with $\sigma>0$, $\gamma>0$, $T>0$ and a real Brownian motion $B$, let $\hat\pi(\tau,y)=p(\tau)$ be an admissible deterministic policy ($p$ measurable). Fix $t\in[0,T)$, $0<h\le T-t$ and $v\in\mathbb R$, and suppose the perturbation $\pi^{h,v}$ ($v$ on $[t,t+h)$, $\hat\pi$ afterwards) is admissible. Then for every starting log-wealth $y$,
--   $$J(t,y;\pi^{h,v}) = J(t,y;\hat\pi)+\int_t^{t+h}\Big(\Big[v(\mu-r)-\frac{1+\gamma}2v^2\sigma^2\Big]-\Big[p(s)(\mu-r)-\frac{1+\gamma}2p(s)^2\sigma^2\Big]\Big)ds .$$
--
--   The effect of a perturbation on the reward is local: it is the integral over the perturbation window of the difference of the instantaneous quadratic objective at $v$ and at $\hat\pi$.
--
--   **Formalization Note** The restriction $h\le T-t$ keeps $t+h$ inside the horizon (for larger $h$ the integral would run to $T$). The page's bracket writes $\hat\pi(\mu-r)$ for $\hat\pi_s(\mu-r)$. The coordinates of $B$ are assumed measurable.
-- source:
--   Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O-11, Proof of Theorem 2 (App. C.2), third display

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_LogMeanVar_Complete_Market
import Definitions.Def_LogMeanVar_Complete_LogReturn
import Definitions.Def_LogMeanVar_Complete_Equilibrium

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace LogMeanVar.Complete

/-- Dai, Jin, Kou, Xu, A Dynamic Mean-Variance Analysis for Log Returns, SSRN 3437268 (version of Aug 2019), p. O–11, Proof of Theorem 2 (App. C.2), third display: for an admissible
deterministic policy `π̂_s = p(s)` and the perturbation
`π^{h,v}_s = v 1_{s∈[t,t+h)} + π̂_s 1_{s∈[t+h,T]}` (also admissible), with `0 < h ≤ T - t`,
`J(t, R_t; π^{h,v}) = J(t, R_t; π̂)
  + ∫_t^{t+h} ([v(μ - r) - (1+γ)/2 v²σ²] - [π̂_s(μ - r) - (1+γ)/2 π̂_s²σ²]) ds`.

**Formalization Note** `h ≤ T - t` keeps `t + h` inside the horizon (for larger `h` the
integral runs to `T`). The printed bracket writes `π̂(μ - r)` for `π̂_s(μ - r)`. -/
theorem c2_spike_decomposition (M : Market) (hM : M.Standing) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P)
    (hBm : ∀ s, Measurable (B s)) (p : ℝ → ℝ) (hp : Measurable p)
    (hadm : Admissible M P B (fun τ _ => p τ)) (t : ℝ) (ht : t ∈ Ico 0 M.T) (h : ℝ)
    (hh : 0 < h) (hhT : h ≤ M.T - t) (v : ℝ)
    (hadm' : Admissible M P B (spike (fun τ _ => p τ) t h v)) (y : ℝ) :
    J M P B (spike (fun τ _ => p τ) t h v) t y =
      J M P B (fun τ _ => p τ) t y +
        ∫ s in t..(t + h),
          ((v * (M.μ - M.r) - (1 + M.γ) / 2 * v ^ 2 * M.σ ^ 2) -
            (p s * (M.μ - M.r) - (1 + M.γ) / 2 * p s ^ 2 * M.σ ^ 2)) := by sorry

end LogMeanVar.Complete
