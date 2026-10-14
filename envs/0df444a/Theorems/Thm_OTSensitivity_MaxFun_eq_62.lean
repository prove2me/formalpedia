-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_eq_62
-- name    : OTSensitivity.MaxFun.eq_62
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:34.10927+00:00
-- url     : https://prove2.me/theorems/4187014b-b01c-4beb-b5f3-1fc118eb7f8a
-- title:
--   (62), p. 34 — ∫ K(ν, δ_y) dν(y) = ∫_𝖷 ∫ K(ν, δ_y) dν^𝓕_x(y) dµ(x)
-- statement:
--   Let $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ be measurable maps from a probability space $(\Omega,\mathcal B,P)$ into Polish spaces, with laws $\mu$ and $\nu$. Let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$, let $\mathcal F$ be a sub-$\sigma$-algebra of the Borel sets of $\mathsf X$, and let $(\nu^{\mathcal F}_x)_{x\in\mathsf X}$ be any version of the conditional distribution of $Y$ given $(X,\mathcal F)$. Then
--
--   $$\int_{\mathsf Y}K(\nu,\delta_y)\,d\nu(y)=\int_{\mathsf X}\Big(\int_{\mathsf Y}K(\nu,\delta_y)\,d\nu^{\mathcal F}_x(y)\Big)\,d\mu(x).$$
--
--   This disintegrates the law of the output along the conditional laws. In the proof of Theorem 5 the left side equals $\mathbb M^K[Y]$, and comparing it with $\xi^K(Y,X\mid\mathcal F)=\int K(\nu,\nu^{\mathcal F}_x)\,d\mu(x)$ is how the equality case is localized to almost every $x$.
--
--   **Formalization Note** $\mathsf X$ and $\mathsf Y$ are Polish (the paper's supports in $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ are such spaces); all values lie in $[0,+\infty]$. The conditional distribution is any Markov kernel satisfying the characterizing predicate `IsCondDistrib`, and the identity holds for every version. $K$ is the published `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 5, (62), p. 34

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- (62), p. 34: disintegration of the law `ν` of `Y` along a version `κ` of the conditional
distribution of `Y` given `(X, 𝓕)`, applied to `y ↦ K(ν, δ_y)`:
`∫ K(ν, δ_y) dν(y) = ∫_𝒳 (∫ K(ν, δ_y) dν^𝓕_x(y)) dµ(x)`. -/
theorem eq_62 {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (F : MeasurableSpace 𝒳) (hF : F ≤ m𝒳) (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib P X Y F κ) :
    ∫⁻ y, RWPI.SqrtLasso.transportCost k (P.map Y) (Measure.dirac y) ∂(P.map Y) =
      ∫⁻ x, ∫⁻ y, RWPI.SqrtLasso.transportCost k (P.map Y) (Measure.dirac y) ∂(κ x) ∂(P.map X) := by sorry

end OTSensitivity.MaxFun
