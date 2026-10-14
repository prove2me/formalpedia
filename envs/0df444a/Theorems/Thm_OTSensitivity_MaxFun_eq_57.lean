-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_eq_57
-- name    : OTSensitivity.MaxFun.eq_57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:27.366382+00:00
-- url     : https://prove2.me/theorems/ccc1784b-5c44-4583-a708-d511e79323cc
-- title:
--   (57), p. 33 — K(ν, ν′) ≤ 𝒦(ν × ν′): the product coupling bounds the optimal transport cost
-- statement:
--   Let $\mathsf Y$ be a Polish space and let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$. For probability measures $\nu,\nu'$ on $\mathsf Y$, let $K(\nu,\nu')$ be the optimal transport cost (1). Then
--
--   $$K(\nu,\nu')\le\int_{\mathsf Y}\int_{\mathsf Y}k(y,y')\,d\nu'(y')\,d\nu(y)=\mathcal K(\nu\times\nu').$$
--
--   The product measure $\nu\times\nu'$ is always a coupling of $\nu$ and $\nu'$, and its cost is the right-hand side. This is the first step of the proof of Theorem 5: integrated against the law of the input it yields the upper bound $\xi^K(Y,X\mid\mathcal F)\le\mathbb M^K[Y]$.
--
--   **Formalization Note** $K$ is the published `RWPI.SqrtLasso.transportCost`, values in $[0,+\infty]$; the right-hand side is an iterated lower Lebesgue integral and may be $+\infty$. $\mathsf Y$ is Polish with its Borel $\sigma$-algebra, which contains the paper's support in $\mathbb R^{n_Y}$.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 5, (57), p. 33

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- (57), p. 33: the product coupling bounds the optimal transport cost,
`K(ν, ν') ≤ ∫∫ k(y, y') dν(y) dν'(y') = 𝒦(ν × ν')`. -/
theorem eq_57 {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν ν' : Measure 𝒴) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    RWPI.SqrtLasso.transportCost k ν ν' ≤ ∫⁻ y, ∫⁻ y', k y y' ∂ν' ∂ν := by sorry

end OTSensitivity.MaxFun
