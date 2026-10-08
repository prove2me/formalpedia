-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_eq_7_1
-- name    : NetTraffic.OnOffFBM.eq_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:29.107554+00:00
-- url     : https://prove2.me/theorems/7055dec3-9949-4e1c-b8b6-0543e8bf26a5
-- title:
--   (7.1), p. 61 — Var(G_T) ∼ σ₀² T^{3−α} L_on(T)
-- statement:
--   Let $W$ be the stationary ON/OFF process of one source with period laws satisfying (2.1)–(2.2), and let
--   $$G_T=\int_0^T(W_u-EW_u)\,du$$
--   be its centred cumulative workload. Then, as $T\to\infty$,
--   $$\mathrm{Var}(G_T)\sim\sigma_0^2\,T^{3-\alpha}L_{\mathrm{on}}(T),\qquad \sigma_0^2=\frac{2\mu_{\mathrm{off}}^2\Gamma(2-\alpha)/(\alpha-1)}{\mu^3\Gamma(4-\alpha)},$$
--   where $L_{\mathrm{on}}(T)=T^\alpha\bar F_{\mathrm{on}}(T)$ and $\mu=\mu_{\mathrm{on}}+\mu_{\mathrm{off}}$.
--
--   The paper cites this asymptotic from Willinger, Taqqu, Sherman and Wilson (1995). It fixes the normalisation $d_T$ of Theorem 4 and the constant $\sigma_0$ of the limit: summing $M$ independent copies gives variance $\sim\sigma_0^2d_T^2$.
--
--   **Formalization Note** "$\sim$" is stated as the ratio tending to $1$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 61, (7.1) and the definition of σ₀² (cited from Willinger, Taqqu, Sherman and Wilson 1995)

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- (7.1), p. 61 (cited by the paper from Willinger, Taqqu, Sherman and Wilson [50]): the centred
cumulative workload `G_T = ∫_0^T (W_u - EW_u) du` of one stationary ON/OFF source satisfies
`Var(G_T) ∼ σ_0² T^{3-α} L_on(T)` as `T → ∞`. -/
theorem eq_7_1
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s) :
    Tendsto (fun T => variance (s.G P T) P / (sigma0sq Fon Foff α * T ^ (3 - α) * Lsv Fon α T))
      atTop (𝓝 1) := by sorry

end NetTraffic.OnOffFBM
