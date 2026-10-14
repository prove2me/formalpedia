-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_dirac_average_bound
-- name    : OTSensitivity.MaxFun.dirac_average_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:30.43009+00:00
-- url     : https://prove2.me/theorems/beb758a1-b104-4cd9-adae-e7e3acd04505
-- title:
--   Proof of Theorem 5, p. 34 — K(ν, ν′) ≤ ∫ K(ν, δ_y) dν′(y)
-- statement:
--   Let $\mathsf Y$ be a Polish space and $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ continuous with $k(y,y')=0\iff y=y'$. For all probability measures $\nu,\nu'$ on $\mathsf Y$,
--
--   $$K(\nu,\nu')\le\int_{\mathsf Y}K(\nu,\delta_y)\,d\nu'(y).$$
--
--   The paper uses this with $\nu$ the law of the output and $\nu'=\nu^{\mathcal F}_x$ a conditional law, "for every $x$". It says that $K(\nu,\cdot)$ lies below the average of its values at Dirac masses; combined with (62) it shows that $\xi^K(Y,X\mid\mathcal F)=\mathbb M^K[Y]$ forces equality for almost every $x$, which is (63).
--
--   **Formalization Note** The statement is given for every probability measure $\nu'$, which contains the page's instance $\nu'=\nu^{\mathcal F}_x$ for each $x$. $K$ is the published `RWPI.SqrtLasso.transportCost`; values lie in $[0,+\infty]$.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 5, display before (63), p. 34

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- Proof of Theorem 5, p. 34, display before (63): `K(ν, ·)` lies below the average of its values
at Dirac masses, `K(ν, ν') ≤ ∫ K(ν, δ_y) dν'(y)`, for every probability measure `ν'` (the page
applies it to `ν' = ν^𝓕_x`). -/
theorem dirac_average_bound {𝒴 : Type*} [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴]
    [BorelSpace 𝒴] (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (ν ν' : Measure 𝒴) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] :
    RWPI.SqrtLasso.transportCost k ν ν' ≤
      ∫⁻ y, RWPI.SqrtLasso.transportCost k ν (Measure.dirac y) ∂ν' := by sorry

end OTSensitivity.MaxFun
