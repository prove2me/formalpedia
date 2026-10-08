-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_eq_2_5
-- name    : NetTraffic.OnOffFBM.eq_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:34.415492+00:00
-- url     : https://prove2.me/theorems/3340786c-d64c-45e0-bab9-dd6181c4fe81
-- title:
--   (2.5), p. 27 — γ_W(h) ∼ μ_off²/((α − 1)μ³) h^{−(α−1)} L_on(h) = (const) h F̄_on(h)
-- statement:
--   Let $W$ be the stationary ON/OFF process of one source with period laws satisfying (2.1) and $\alpha=\alpha_{\mathrm{on}}<\alpha_{\mathrm{off}}$ (2.2), and let $\gamma_W(h)=\mathrm{Cov}(W_0,W_h)$ be its covariance function. Then, as $h\to\infty$,
--   $$\gamma_W(h)\sim\frac{\mu_{\mathrm{off}}^2}{(\alpha-1)\mu^3}\,h^{-(\alpha-1)}L_{\mathrm{on}}(h),$$
--   where $L_{\mathrm{on}}(h)=h^\alpha\bar F_{\mathrm{on}}(h)$; moreover $h^{-(\alpha-1)}L_{\mathrm{on}}(h)=h\bar F_{\mathrm{on}}(h)$ for $h>0$.
--
--   The paper cites this asymptotic from Heath, Resnick and Samorodnitsky (1998). It is the long-range dependence of a single source: $\gamma_W$ is regularly varying with index $1-\alpha\in(-1,0)$ and so not summable. Integrated twice it gives the variance asymptotic (7.1).
--
--   **Formalization Note** "$\sim$" is stated as the ratio tending to $1$. $\gamma_W(h)$ is taken at time origin $0$; by stationarity $\mathrm{Cov}(W_t,W_{t+h})$ does not depend on $t$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 27, (2.5) (cited from Heath, Resnick and Samorodnitsky 1998)

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- (2.5), p. 27 (cited by the paper from Heath, Resnick and Samorodnitsky [18]): under (2.1)
and `α_on < α_off`, the covariance function `γ_W(h) = Cov(W_0, W_h)` of the stationary ON/OFF
process satisfies `γ_W(h) ∼ μ_off²/((α-1)μ³) h^{-(α-1)} L_on(h)` as `h → ∞`, and
`h^{-(α-1)} L_on(h) = h F̄_on(h)` for `h > 0`. -/
theorem eq_2_5
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s) :
    Tendsto (fun h => gammaW P s h /
        (mean Foff ^ 2 / ((α - 1) * mu Fon Foff ^ 3) * h ^ (-(α - 1)) * Lsv Fon α h))
      atTop (𝓝 1) ∧
    ∀ h : ℝ, 0 < h → h ^ (-(α - 1)) * Lsv Fon α h = h * Fbar Fon h := by sorry

end NetTraffic.OnOffFBM
