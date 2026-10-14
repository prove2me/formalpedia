-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_proposition_3
-- name    : OTSensitivity.MaxFun.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:35.822456+00:00
-- url     : https://prove2.me/theorems/d365535a-71d8-4a8d-ab78-0f528b00673d
-- title:
--   Proposition 3 — zero-independence: ξ^K(Y, X) = 0 iff X and Y are independent
-- statement:
--   Let $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ be measurable maps from a probability space $(\Omega,\mathcal B,P)$ into Polish spaces, with laws $\mu$ and $\nu$, and let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$. Let $(\nu_x)_{x\in\mathsf X}$ be any version of the conditional distribution of $Y$ given $X$ (that is, given the whole Borel $\sigma$-algebra of $\mathsf X$), and $\xi^K(Y,X)=\int K(\nu,\nu_x)\,d\mu(x)$. Then $\xi^K(Y,X)\ge0$, and
--
--   $$\xi^K(Y,X)=0\iff X\text{ and }Y\text{ are independent}.$$
--
--   This is the zero-independence property of the OT-based sensitivity measures: the measure detects every form of statistical dependence of the output on the input, not only dependence in the mean.
--
--   **Formalization Note** Since values lie in $[0,+\infty]$, the inequality $\xi^K(Y,X)\ge0$ holds by construction and only the equivalence is stated. No finiteness of $\mathbb M^K[Y]$ is assumed, as on the page. $\mathsf X$ and $\mathsf Y$ are Polish (the paper's supports in $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ are such spaces); the conditional distribution is any kernel satisfying `IsCondDistrib` for the Borel $\sigma$-algebra, and the statement holds for every version. Independence is Mathlib's `IndepFun X Y P`. $K$ is the published `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Proposition 3, p. 9; proof p. 32

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- Proposition 3, p. 9 (zero-independence): with `𝓕 = 𝓑(𝒳)`, `ξ^K(Y, X) = 0` if and only if
`X` and `Y` are independent. (`ξ^K(Y, X) ≥ 0` is automatic in `ℝ≥0∞`.) -/
theorem proposition_3 {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib P X Y m𝒳 κ) :
    xi k P X Y κ = 0 ↔ IndepFun X Y P := by sorry

end OTSensitivity.MaxFun
