-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_eq_4_14
-- name    : NetTraffic.PoissonFBM.eq_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:46.214992+00:00
-- url     : https://prove2.me/theorems/bae3d446-29be-4584-a03a-f8dcba0eb9e3
-- title:
--   (4.14), p. 36 — σ₃² = (1/μ_on)∫₀^∞∫_s^{1+s} (y−s)² αy^{−α−1} dy ds = 1/(μ_on(3−α))
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, and let $\mu_{\mathrm{on}}$ be its mean. Then
--   $$\sigma_3^2:=\frac1{\mu_{\mathrm{on}}}\int_{s=0}^\infty\int_{y=s}^{1+s}(y-s)^2\,\alpha y^{-\alpha-1}\,dy\,ds=\frac1{\mu_{\mathrm{on}}(3-\alpha)} .$$
--
--   This constant is the limit of $\mathrm{Var}(j_3+t_3)/(T^3\bar F_{\mathrm{on}}(T))$ for the transmissions that start before $0$ and end in $(0,T]$; multiplied by $\lambda m_3\sim\lambda\mu_{\mathrm{on}}$ it gives the $A_3$ part $1/(3-\alpha)$ of the limit variance.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 36, (4.14)

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- (4.14), p. 36: `σ_3² := (1/μ_on) ∫_0^∞ ∫_s^{1+s} (y - s)² α y^{-α-1} dy ds = 1/(μ_on(3 - α))`. -/
theorem eq_4_14
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α) :
    (1 / NetTraffic.PoissonStable.muOn Fon) * ∫ s in Set.Ioi (0 : ℝ), ∫ y in Set.Ioc s (1 + s),
        (y - s) ^ 2 * α * y ^ (-α - 1) =
      1 / (NetTraffic.PoissonStable.muOn Fon * (3 - α)) := by sorry

end NetTraffic.PoissonFBM
