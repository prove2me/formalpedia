-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_Supplement_theorem_19
-- name    : OTSensitivity.MaxFun.Supplement.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:29:22.227807+00:00
-- url     : https://prove2.me/theorems/42b643e4-4077-4087-a288-7ed0c87a6669
-- title:
--   Theorem 19 (corrected: finite normalizer) — the entropic sensitivity index tends to one as regularization grows
-- statement:
--   Let $\mathsf X$, $\mathsf Y$ be Polish spaces with their Borel σ-algebras, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable on a probability space $(\Omega,P)$, $\nu$ the law of $Y$, and $k$ a cost that is continuous into $[0,+\infty]$ and vanishes exactly on the diagonal. Assume $0<\mathbb M^K[Y]<\infty$, where $\mathbb M^K[Y]=\int\!\int k\,d\nu\,d\nu$ (18). The **entropic OT-based sensitivity index** (31) of Definition 13 is
--
--   $$\iota_\varepsilon(Y,X)=\frac{\xi^{K_\varepsilon}(Y,X)}{\mathbb M^K[Y]},$$
--
--   with $\xi^{K_\varepsilon}(Y,X)=\int K_\varepsilon(\nu,\nu_x)\,d\mu(x)$ computed from any version $(\nu_x)$ of the conditional distribution of $Y$ given $X$. Then
--
--   $$\lim_{\varepsilon\to\infty}\iota_\varepsilon(Y,X)=1.$$
--
--   For large regularization every input becomes maximally important: the entropic index loses its discriminating power. It is a companion result of the paper and is not used in the proof of Theorem 5.
--
--   **Formalization Note** The quotient is computed in `ℝ≥0∞`, where it is a number because $0<\mathbb M^K[Y]<\infty$; $\varepsilon$ ranges over `ℝ≥0` along `atTop`. The input $X$ ranges over every measurable map into every Polish space.
--
--   Differences from the source:
--   - correction: $\iota_\varepsilon=\xi^{K_\varepsilon}/\mathbb M^K[Y]$, defined when $\mathbb M^K[Y]>0$ (Definition 13) → additionally $\mathbb M^K[Y]<\infty$; reason: Definition 13 explicitly requires only positivity, but its quotient needs a finite normalizer: in ℝ≥0∞ every value divided by ∞ is zero, so (47) fails under that totalized reading. Restricting to $0<\mathbb M^K[Y]<\infty$ repairs this undefined boundary of the printed quotient; no finite positive instance is excluded
--   - reading: "Given ιε(Y, Xi) in Equation (31) … for any X" → $\iota_\varepsilon(Y,X)$ for every measurable input $X$ in every Polish space; reason: the subscript $i$ in $X_i$ is the notation of the paper's examples; the claim is for any input $X$
--   - reading: the result names no cost assumption, or only "k continuous" → `IsCost k`: $k$ continuous into $[0,+\infty]$ and $k(y,y')=0\iff y=y'$; reason: this is the standing cost assumption of §3.1 (p. 9), under which every result of the section is stated
--   - encoding: the conditional distribution $\nu^{\mathcal F}_x$ of $Y$ given $(X,\mathcal F)$ → every Markov kernel satisfying the defining property `OTSensitivity.Info.IsCondDistrib`; reason: versions agree $\mu$-a.e. and exist on Polish spaces, so stating the result for every version is the page's statement
--   - generalization: the supports of the random variables are subsets of $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ (pp. 4, 7) → the spaces are arbitrary Polish spaces with their Borel σ-algebras; reason: closed subsets of Euclidean space are Polish, so the paper's setting is an instance; the same convention as the published base mission
--   - encoding: values of $k$, $K$, $K_\varepsilon$, KL in $[0,+\infty]$ → values in `ℝ≥0∞`; KL is Mathlib's `InformationTheory.klDiv`; reason: for probability measures `klDiv` is $+\infty$ off absolute continuity and $\int\log\frac{d\pi}{d\vartheta}\,d\pi$ otherwise, which is (7); same instances
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 19, (47), p. 16; Definition 13, (31), p. 12; proof p. 38

import Mathlib
import Definitions.Def_OTSensitivity_MaxFun_Setting
import Definitions.Def_OTSensitivity_Info_Setting
import Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.MaxFun.Supplement

/-- Theorem 19, p. 16: for every input `X`, the entropic index (31)
`ι_ε(Y, X) = ξ^{K_ε}(Y, X) / 𝕄^K[Y]` tends to `1` as `ε → ∞` (47). The index is defined when
`0 < 𝕄^K[Y]` (Definition 13) and `𝕄^K[Y] < ∞`; `ξ^{K_ε}(Y, X)` is computed from any version `κ`
of the conditional distribution of `Y` given `X` (`𝓕 = 𝓑(𝒳)`). -/
theorem theorem_19 {Ω 𝒳 𝒴 : Type*} [MeasurableSpace Ω]
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (hMK0 : 0 < OTSensitivity.MaxFun.MK k (P.map Y))
    (hMK : OTSensitivity.MaxFun.MK k (P.map Y) < ⊤)
    (κ : Kernel 𝒳 𝒴) (hκ : OTSensitivity.Info.IsCondDistrib P X Y m𝒳 κ) :
    Tendsto (fun ε : ℝ≥0 => xiEps k ε P X Y κ / OTSensitivity.MaxFun.MK k (P.map Y)) atTop
      (𝓝 1) := by sorry

end OTSensitivity.MaxFun.Supplement
