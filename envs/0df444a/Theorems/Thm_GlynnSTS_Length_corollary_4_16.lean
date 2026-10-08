-- Prove2me | Theorems.Thm_GlynnSTS_Length_corollary_4_16
-- name    : GlynnSTS.Length.corollary_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:05.007977+00:00
-- url     : https://prove2.me/theorems/c550e836-b1e4-4f91-895f-d871d99ebdd5
-- title:
--   Corollary 4.16 — universal STS expected-length lower bound
-- statement:
--   Let $g\in\mathcal M$ be nonnegative on $C[0,1]$, and suppose Assumption (2.1) holds for the output process, with Brownian scale $\sigma>0$. Choose $0<\delta<1$ and $\alpha,\beta$ so that $H(\beta)-H(\alpha)=1-\delta$. If $L_n=g(\overline Y_n)(\beta-\alpha)$ is the length of the STS interval, then
--   $$
--   \liminf_{n\to\infty}\sqrt n\,E[L_n]\ge
--   2\sigma\Phi^{-1}(1-\delta/2).
--   $$
--   This is the paper's universal lower bound for the expected length of an asymptotic STS confidence interval.
--
--   **Formalization Note** The normal quantile is supplied as $p$ with $\Phi(p)=1-\delta/2$. Extended nonnegative expectations retain the case $E[L_n]=+\infty$. The process is measurable and integrable on finite intervals so its integrated average is defined.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 12, Corollary 4.16

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTS.Length

/-- Corollary 4.16, p. 12: every nonnegative STS interval has the normal-quantile lower bound. -/
theorem corollary_4_16 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (hg0 : ∀ x, 0 ≤ g x)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (h21 : Assumption21 P Y Ybar μ σ B)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (α β : ℝ) (hαβ : H P B g β - H P B g α = 1 - δ)
    (p : ℝ) (hp : cdf (gaussianReal 0 1) p = 1 - δ / 2) :
    ENNReal.ofReal (2 * σ * p) ≤
      liminf (fun n : ℕ => ENNReal.ofReal (Real.sqrt n) *
        ∫⁻ ω, ENNReal.ofReal (Ln g Ybar α β n ω) ∂P) atTop := by sorry

end GlynnSTS.Length
