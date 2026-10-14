-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_transportCost_dirac
-- name    : OTSensitivity.MaxFun.transportCost_dirac
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:26.560767+00:00
-- url     : https://prove2.me/theorems/581b9d58-03d5-4125-bf01-7dfdca3449a1
-- title:
--   Proof of Theorem 5, p. 33 — K(ν, δ_{y′}) = ∫ k(y, y′) dν(y)
-- statement:
--   Let $\mathsf Y$ be a Polish space, $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $k(y,y')=0\iff y=y'$, and $\nu$ a probability measure on $\mathsf Y$. For every point $y'\in\mathsf Y$, the optimal transport cost from $\nu$ to the Dirac mass $\delta_{y'}$ is
--
--   $$K(\nu,\delta_{y'})=\int_{\mathsf Y}k(y,y')\,d\nu(y).$$
--
--   The only coupling of $\nu$ with $\delta_{y'}$ is $\nu\times\delta_{y'}$, so the infimum in (1) is taken over one plan. The identity turns $\mathbb M^K[Y]$ into $\int K(\nu,\delta_y)\,d\nu(y)$, which is how the proof of Theorem 5 identifies the maximum, and it is the same computation as (69), p. 36.
--
--   **Formalization Note** $K$ is the published `RWPI.SqrtLasso.transportCost`, with the marginal $\nu$ as first argument and the cost evaluated as $k(y,y')$, $y\sim\nu$; $k$ is not assumed symmetric. Values lie in $[0,+\infty]$, so both sides may be $+\infty$.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 5, display K(ν, δ_{f(x)}) = ∫ k(y, f(x)) dν(y), p. 33; see also (69), p. 36

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- Proof of Theorem 5, p. 33 (and (69), p. 36): the only coupling of `ν` with a Dirac mass
`δ_{y'}` is `ν × δ_{y'}`, so `K(ν, δ_{y'}) = ∫ k(y, y') dν(y)`. -/
theorem transportCost_dirac {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν : Measure 𝒴) [IsProbabilityMeasure ν] (y' : 𝒴) :
    RWPI.SqrtLasso.transportCost k ν (Measure.dirac y') = ∫⁻ y, k y y' ∂ν := by sorry

end OTSensitivity.MaxFun
