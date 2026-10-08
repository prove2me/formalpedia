-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_eq_4_9
-- name    : NetTraffic.PoissonFBM.eq_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:41.795118+00:00
-- url     : https://prove2.me/theorems/dd63e332-ce0a-48c2-93f0-fb1b85ed3f2e
-- title:
--   (4.9), p. 35 — Var(j₁)/(T² F̄_on(T)) → α/((2−α)(3−α)) = σ₁²
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$. For $T>0$ let $j_1$ be a random variable with the law (4.4) on the region $R_1=\{(s,y):0<s\le T,\ y>0,\ s+y\le T\}$, i.e. the length of a transmission drawn from $\mathbb L(ds)F_{\mathrm{on}}(dy)/m_1$ restricted to $R_1$. Then
--   $$\lim_{T\to\infty}\frac{\mathrm{Var}(j_1)}{T^2\,\bar F_{\mathrm{on}}(T)}=\int_0^1\!\!\int_0^s y^2\,\alpha y^{-1-\alpha}\,dy\,ds=\frac{\alpha}{(2-\alpha)(3-\alpha)}=:\sigma_1^2 .$$
--
--   This is the variance of the summands of $A_1$, the input of transmissions that start and end inside $(0,T]$; it gives the $A_1$ part of the limit variance.
--
--   **Formalization Note** The page writes "$\sim$" against a constant; it is a limit. $\mathrm{Var}(j_1)$ is the variance of the identity under the law of $j_1$ (a deterministic quantity).
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 35, (4.9)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- (4.9), p. 35: `Var(j_1)/(T² F̄_on(T)) → α/((2-α)(3-α)) = σ_1²` as `T → ∞`, where `j_1` has the
law (4.4) on `R_1`. -/
theorem eq_4_9
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α) :
    Tendsto (fun T => variance id (NetTraffic.PoissonStable.j1Law Fon T) / (T ^ 2 * NetTraffic.PoissonStable.Fbar Fon T)) atTop
      (𝓝 (sigma1sq α)) := by sorry

end NetTraffic.PoissonFBM
