-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_theorem_5
-- name    : OTSensitivity.MaxFun.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:31.538341+00:00
-- url     : https://prove2.me/theorems/127887cb-157b-40a3-be68-543863d93890
-- title:
--   Theorem 5 — ξ^K(Y, X|𝓕) ≤ 𝕄^K[Y], with equality iff Y = f(X) a.s. for an 𝓕-measurable f
-- statement:
--   Let $(\Omega,\mathcal B,P)$ be a probability space, $\mathsf X$ and $\mathsf Y$ Polish spaces, and $X:\Omega\to\mathsf X$, $Y:\Omega\to\mathsf Y$ measurable, with laws $\mu$ and $\nu$. Let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$, and assume
--
--   $$\mathbb M^K[Y]=\int_{\mathsf Y}\int_{\mathsf Y}k(y,y')\,d\nu(y')\,d\nu(y)<+\infty.$$
--
--   Let $\mathcal F$ be any sub-$\sigma$-algebra of the Borel sets of $\mathsf X$ and $(\nu^{\mathcal F}_x)_x$ any version of the conditional distribution of $Y$ given $(X,\mathcal F)$, and let $\xi^K(Y,X\mid\mathcal F)=\int_{\mathsf X}K(\nu,\nu^{\mathcal F}_x)\,d\mu(x)$. Then
--
--   1. $\xi^K(Y,X\mid\mathcal F)\le\mathbb M^K[Y]$ (equation (20)); in particular $\xi^K(Y,X\mid\mathcal F)$ is finite;
--   2. $\xi^K(Y,X\mid\mathcal F)=\mathbb M^K[Y]$ if and only if $Y$ is functionally dependent on $X$ through $\mathcal F$, that is, $Y=f(X)$ $P$-almost surely for some $\mathcal F$-measurable map $f:\mathsf X\to\mathsf Y$.
--
--   This is the max-functionality property (Rényi's Postulate E) of OT-based sensitivity measures: the measure is bounded by an explicit constant of the output's law, and reaches it exactly when the information carried by $(X,\mathcal F)$ determines the output.
--
--   **Formalization Note** $\mathsf X$ and $\mathsf Y$ are Polish (the paper's supports in $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ are such spaces); all values lie in $[0,+\infty]$. "The assumptions of Lemma 4" are the continuity of $k$, the standing assumption $k(y,y')=0\iff y=y'$ of §3.1, and $\mathcal K(\nu\times\nu)=\mathbb M^K[Y]<\infty$; the finiteness is assumed for the whole theorem, as on the page. The statement holds for every sub-$\sigma$-algebra $\mathcal F$ and every version of the conditional distribution (any kernel satisfying `IsCondDistrib`). $K$ is the published `RWPI.SqrtLasso.transportCost`.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 5 and (20), p. 10; proof pp. 33–34

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSensitivity.MaxFun

/-- Theorem 5, p. 10 (max-functionality): under the assumptions of Lemma 4 (`k` continuous,
vanishing exactly on the diagonal, `𝕄^K[Y] < ∞`), for every sub-σ-algebra `𝓕` of `𝓑(𝒳)` and
every version `κ` of the conditional distribution of `Y` given `(X, 𝓕)`,
`ξ^K(Y, X | 𝓕) ≤ 𝕄^K[Y]` (20), and equality holds if and only if `Y = f(X)` `P`-a.e. for some
`𝓕`-measurable `f : 𝒳 → 𝒴`. -/
theorem theorem_5 {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (hMK : MK k (P.map Y) < ⊤)
    (F : MeasurableSpace 𝒳) (hF : F ≤ m𝒳) (κ : Kernel 𝒳 𝒴) (hκ : IsCondDistrib P X Y F κ) :
    xi k P X Y κ ≤ MK k (P.map Y) ∧
      (xi k P X Y κ = MK k (P.map Y) ↔ IsFunctionallyDependent P X Y F) := by sorry

end OTSensitivity.MaxFun
