-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_eq_63
-- name    : OTSensitivity.MaxFun.eq_63
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:35.463562+00:00
-- url     : https://prove2.me/theorems/d443dfb6-4684-4cfc-b0f4-3cde731766f1
-- title:
--   (63), p. 34 — at the maximum, K(ν, ν^𝓕_x) = ∫ K(ν, δ_y) dν^𝓕_x(y) for µ-a.e. x
-- statement:
--   Let $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ be measurable maps from a probability space $(\Omega,\mathcal B,P)$ into Polish spaces, with laws $\mu$ and $\nu$, and let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$ and $\mathbb M^K[Y]<+\infty$. Let $\mathcal F$ be a sub-$\sigma$-algebra of the Borel sets of $\mathsf X$ and $(\nu^{\mathcal F}_x)_x$ any version of the conditional distribution of $Y$ given $(X,\mathcal F)$. If $\xi^K(Y,X\mid\mathcal F)=\mathbb M^K[Y]$, then
--
--   $$K(\nu,\nu^{\mathcal F}_x)=\int_{\mathsf Y}K(\nu,\delta_y)\,d\nu^{\mathcal F}_x(y)\qquad\text{for }\mu\text{-a.e. }x\in\mathsf X.$$
--
--   This is the step of the converse of Theorem 5 that turns the global equality into a pointwise one; the remaining argument shows that equality here forces $\nu^{\mathcal F}_x$ to be a Dirac mass.
--
--   **Formalization Note** All values lie in $[0,+\infty]$; the finiteness of $\mathbb M^K[Y]$ is what lets the two integrals be compared. "$\mu$-a.e." is `∀ᵐ x ∂(P.map X)`. The conditional distribution is any kernel satisfying `IsCondDistrib`, and the statement holds for every version. $K$ is the published `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Appendix A, proof of Theorem 5, (61)–(63), p. 34

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- (63), p. 34: if `𝕄^K[Y] < ∞` and `ξ^K(Y, X | 𝓕) = 𝕄^K[Y]`, then
`K(ν, ν^𝓕_x) = ∫ K(ν, δ_y) dν^𝓕_x(y)` for `µ`-a.e. `x`. -/
theorem eq_63 {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (hMK : MK k (P.map Y) < ⊤)
    (F : MeasurableSpace 𝒳) (hF : F ≤ m𝒳) (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib P X Y F κ)
    (hmax : xi k P X Y κ = MK k (P.map Y)) :
    ∀ᵐ x ∂(P.map X), RWPI.SqrtLasso.transportCost k (P.map Y) (κ x) =
      ∫⁻ y, RWPI.SqrtLasso.transportCost k (P.map Y) (Measure.dirac y) ∂(κ x) := by sorry

end OTSensitivity.MaxFun
