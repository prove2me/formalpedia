-- Prove2me | Theorems.Thm_NetTraffic_OnOffFBM_mean_W
-- name    : NetTraffic.OnOffFBM.mean_W
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:41.348227+00:00
-- url     : https://prove2.me/theorems/4b502b3a-98f5-42cb-ac43-a1397bd2b985
-- title:
--   §2.1, p. 27 — the stationary ON/OFF process has mean EW_t = P(W_t = 1) = μ_on/μ
-- statement:
--   Let $W$ be the ON/OFF process of one source, built from the delayed renewal sequence $T_0$, $T_n=T_0+\sum_{i=1}^nZ_i$ of §2.1 with ON-period law $F_{\mathrm{on}}$ and OFF-period law $F_{\mathrm{off}}$ satisfying (2.1)–(2.2), and let $\mu=\mu_{\mathrm{on}}+\mu_{\mathrm{off}}$. Then for every $t\ge0$,
--   $$EW_t=P(W_t=1)=\frac{\mu_{\mathrm{on}}}{\mu}.$$
--
--   The delay $T_0$ makes the renewal sequence, and hence $W$, stationary; this identity is what makes $TM\mu^{-1}\mu_{\mathrm{on}}t$ the mean of the cumulative input $A(Tt)$ of $M$ sources, the centring in Theorem 4.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 27, §2.1, display EW_t = P(W_t = 1) = μ_on/μ

import Mathlib
import Definitions.Def_NetTraffic_OnOffFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.OnOffFBM

/-- §2.1, p. 27: the stationary ON/OFF process of one source has mean
`E W_t = P(W_t = 1) = μ_on/μ` for every `t ≥ 0`. -/
theorem mean_W
    (Fon Foff : Measure ℝ) [IsProbabilityMeasure Fon] [IsProbabilityMeasure Foff]
    (α αoff : ℝ) (hF : HeavyTails Fon Foff α αoff)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Source Ω) (hs : IsOnOffSource P Fon Foff s) :
    ∀ t : ℝ, 0 ≤ t →
      P[s.W t] = mean Fon / mu Fon Foff ∧
        P.real {ω | s.W t ω = 1} = mean Fon / mu Fon Foff := by sorry

end NetTraffic.OnOffFBM
