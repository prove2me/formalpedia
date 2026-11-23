-- Prove2me | Theorems.Thm_OTSensitivity_MaxFun_Supplement_theorem_11
-- name    : OTSensitivity.MaxFun.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:27:55.940803+00:00
-- url     : https://prove2.me/theorems/1d37ef3f-e786-4e34-850c-287949f39b80
-- title:
--   Theorem 11 (corrected: $\mathbb M^K[Y]<\infty$ for the converse of max-functionality) — the entropic index lies between the classical one and $\mathbb M^K[Y]$ and keeps Theorems 5, 8 and 9
-- statement:
--   Let $\mathsf X$, $\mathsf Y$, $\mathsf U$ be Polish spaces with their Borel σ-algebras, $X:\Omega\to\mathsf X$ and $Y:\Omega\to\mathsf Y$ measurable on a probability space $(\Omega,P)$, $\mu$ and $\nu$ the laws of $X$ and $Y$, and $k$ a cost that is continuous into $[0,+\infty]$ and vanishes exactly on the diagonal. Let $\varepsilon>0$, $K_\varepsilon$ the entropic OT functional (8), $\xi^K$ and $\xi^{K_\varepsilon}$ the classical and entropic sensitivity measures, and $\mathbb M^K[Y]=\int\!\int k\,d\nu\,d\nu$ (18). Every conditional distribution below is any version of it. For every sub-σ-algebra $\mathcal F\subseteq\mathcal B(\mathsf X)$:
--
--   1. (27) holds:
--
--   $$\xi^K(Y,X|\mathcal F)\le\xi^{K_\varepsilon}(Y,X|\mathcal F)\le\mathbb M^K[Y],$$
--
--      so $\xi^{K_\varepsilon}(Y,X|\mathcal F)$ is finite if $\mathbb M^K[Y]<\infty$.
--   2. If $Y=f(X)$ $P$-a.e. for some $\mathcal F$-measurable $f:\mathsf X\to\mathsf Y$, then $\xi^{K_\varepsilon}(Y,X|\mathcal F)=\mathbb M^K[Y]$.
--   3. If $\mathbb M^K[Y]<\infty$ and $\xi^{K_\varepsilon}(Y,X|\mathcal F)=\mathbb M^K[Y]$, then $Y=f(X)$ $P$-a.e. for some $\mathcal F$-measurable $f$.
--   4. (Theorem 8, (23)) $\xi^{K_\varepsilon}(Y,X|\mathcal F)\le\xi^{K_\varepsilon}(Y,X)$.
--   5. (Theorem 8, (24)) For a Borel map $g:\mathsf X\to\mathsf U$ and $U=g\circ X$: $\xi^{K_\varepsilon}(Y,U)\le\xi^{K_\varepsilon}(Y,X)$ and $\xi^{K_\varepsilon}(Y,U)=\xi^{K_\varepsilon}(Y,X|\sigma(g))$; if moreover $g$ is injective $\mu$-almost everywhere, $\xi^{K_\varepsilon}(Y,X)=\xi^{K_\varepsilon}(Y,U)$.
--   6. (Theorem 9, (25)) For an increasing sequence $(\mathcal F_n)$ of sub-σ-algebras of $\mathcal B(\mathsf X)$ with join $\bigvee_n\mathcal F_n$, $\lim_{n\to\infty}\xi^{K_\varepsilon}(Y,X|\mathcal F_n)=\xi^{K_\varepsilon}(Y,X|\bigvee_n\mathcal F_n)$ in $[0,+\infty]$.
--
--   The theorem places the entropic measure on the same scale as the classical one, $\xi^K\le\xi^{K_\varepsilon}\le\mathbb M^K$, and shows that it keeps max-functionality, monotonicity in the information and continuity along refining information. It is a companion result of the paper and is not used in the proof of Theorem 5.
--
--   **Formalization Note** All data of the clauses ($\mathcal F$, $g$, $(\mathcal F_n)$ and the versions of the conditional distributions) are parameters of one statement; since versions exist on Polish spaces, this is equivalent to stating each clause separately. The σ-algebra parameters are placed before the ambient instance on $\mathsf X$, so kernels and $\mu$ are typed on $\mathcal B(\mathsf X)$ (checked with `pp.explicit`). Versions are characterized by `OTSensitivity.Info.IsCondDistrib`; "injective $\mu$-a.e." is `OTSensitivity.Info.IsInjectiveAE`, as in the published Theorem 8.
--
--   Differences from the source:
--   - correction: $\xi^{K_\varepsilon}(Y,X|\mathcal F)=\mathbb M^K[Y]$ implies functional dependence, with no finiteness assumption → this direction assumes $\mathbb M^K[Y]<\infty$; the other direction, (27) and the Theorem 8/9 clauses carry no such assumption; reason: the proof (p. 37) reuses the argument of Theorem 5, which is stated under the assumptions of Lemma 4, including $\mathbb M^K[Y]<\infty$. Counterexample without it: $\nu$ symmetric with a positive density and $\mathbb E[Y^2]=\infty$, $k(y,y')=(y-y')^2$, $X=\mathrm{sign}(Y)$; then $\xi^K(Y,X)=\infty$, so by (27) $\xi^{K_\varepsilon}=\mathbb M^K=\infty$, but $Y$ is not a function of $X$. Excluded: only outputs with $\mathbb M^K[Y]=\infty$, and only for this direction
--   - reading: "ξKε(Y, X) satisfies the same properties stated in Theorems 8, and 9" → the clauses (23), (24), the injective case and (25) written out for $\xi^{K_\varepsilon}$; reason: these are the properties stated in Theorems 8 and 9 (p. 11), copied in the shape of the published `OTSensitivity.Info.theorem_8_i`, `theorem_8_ii` and `theorem_9`
--   - reading: the result names no cost assumption, or only "k continuous" → `IsCost k`: $k$ continuous into $[0,+\infty]$ and $k(y,y')=0\iff y=y'$; reason: this is the standing cost assumption of §3.1 (p. 9), under which every result of the section is stated
--   - encoding: the conditional distribution $\nu^{\mathcal F}_x$ of $Y$ given $(X,\mathcal F)$ → every Markov kernel satisfying the defining property `OTSensitivity.Info.IsCondDistrib`; reason: versions agree $\mu$-a.e. and exist on Polish spaces, so stating the result for every version is the page's statement
--   - generalization: the supports of the random variables are subsets of $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ (pp. 4, 7) → the spaces are arbitrary Polish spaces with their Borel σ-algebras; reason: closed subsets of Euclidean space are Polish, so the paper's setting is an instance; the same convention as the published base mission
--   - encoding: values of $k$, $K$, $K_\varepsilon$, KL in $[0,+\infty]$ → values in `ℝ≥0∞`; KL is Mathlib's `InformationTheory.klDiv`; reason: for probability measures `klDiv` is $+\infty$ off absolute continuity and $\int\log\frac{d\pi}{d\vartheta}\,d\pi$ otherwise, which is (7); same instances
--   - encoding: the independently universally quantified information, transformation and increasing-σ-algebra clauses → all clause data and conditional kernels are theorem parameters before the conjunction of conclusions; reason: each source instance is recovered by taking the auxiliary transformation to be the identity and the auxiliary σ-algebra sequence constant when those clauses are unused; the requisite versions exist for Polish outputs. σ-algebras precede the ambient instance to prevent instance capture
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 11, (27), p. 11; proof p. 37; Theorems 8 and 9, (23)–(25), p. 11

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_MaxFun_Setting
import Definitions.Def_OTSensitivity_Info_Setting
import Definitions.Def_OTSensitivity_Info_InjectiveAE
import Definitions.Def_OTSensitivity_MaxFun_Supplement_Entropic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.MaxFun.Supplement

/-- Theorem 11, p. 11, for `ε > 0`:
1. (27) `ξ^K(Y, X | 𝓕) ≤ ξ^{K_ε}(Y, X | 𝓕) ≤ 𝕄^K[Y]`, so `ξ^{K_ε}(Y, X | 𝓕) < ∞` if `𝕄^K[Y] < ∞`;
2. functional dependence on `(X, 𝓕)` implies `ξ^{K_ε}(Y, X | 𝓕) = 𝕄^K[Y]`; conversely, if
   `𝕄^K[Y] < ∞` (disclosed correction: the assumption of Theorem 5), equality implies functional
   dependence;
3. the analogues of Theorem 8 for `ξ^{K_ε}`: (23) `ξ^{K_ε}(Y, X | 𝓕) ≤ ξ^{K_ε}(Y, X)`; (24)
   `ξ^{K_ε}(Y, g ∘ X) ≤ ξ^{K_ε}(Y, X)` and `ξ^{K_ε}(Y, g ∘ X) = ξ^{K_ε}(Y, X | σ(g))` for a Borel
   `g : 𝒳 → 𝒰` into a Polish space; equality `ξ^{K_ε}(Y, X) = ξ^{K_ε}(Y, g ∘ X)` when `g` is
   injective `µ`-a.e.;
4. the analogue of Theorem 9: `ξ^{K_ε}(Y, X | 𝓕ₙ) → ξ^{K_ε}(Y, X | ⋁ₙ 𝓕ₙ)` for increasing `(𝓕ₙ)`.
Every statement holds for every version of every conditional distribution involved. -/
theorem theorem_11 {Ω 𝒳 𝒴 𝒰 : Type*} [MeasurableSpace Ω]
    (F : MeasurableSpace 𝒳) (Fs : ℕ → MeasurableSpace 𝒳)
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [m𝒳 : MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    [TopologicalSpace 𝒰] [PolishSpace 𝒰] [m𝒰 : MeasurableSpace 𝒰] [BorelSpace 𝒰]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : OTSensitivity.MaxFun.IsCost k)
    (ε : ℝ≥0) (hε : 0 < ε)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → 𝒳) (Y : Ω → 𝒴) (hX : Measurable X) (hY : Measurable Y)
    (hF : F ≤ m𝒳) (κF : Kernel 𝒳 𝒴) (hκF : OTSensitivity.Info.IsCondDistrib P X Y F κF)
    (κ : Kernel 𝒳 𝒴) (hκ : OTSensitivity.Info.IsCondDistrib P X Y m𝒳 κ)
    (g : 𝒳 → 𝒰) (hg : Measurable g)
    (κU : Kernel 𝒰 𝒴) (hκU : OTSensitivity.Info.IsCondDistrib P (g ∘ X) Y m𝒰 κU)
    (κg : Kernel 𝒳 𝒴)
    (hκg : OTSensitivity.Info.IsCondDistrib P X Y (MeasurableSpace.comap g m𝒰) κg)
    (hmono : Monotone Fs) (hle : ∀ n, Fs n ≤ m𝒳)
    (κs : ℕ → Kernel 𝒳 𝒴) (hκs : ∀ n, OTSensitivity.Info.IsCondDistrib P X Y (Fs n) (κs n))
    (κsup : Kernel 𝒳 𝒴) (hκsup : OTSensitivity.Info.IsCondDistrib P X Y (⨆ n, Fs n) κsup) :
    -- (27) and the finiteness remark
    (OTSensitivity.MaxFun.xi k P X Y κF ≤ xiEps k ε P X Y κF ∧
      xiEps k ε P X Y κF ≤ OTSensitivity.MaxFun.MK k (P.map Y) ∧
      (OTSensitivity.MaxFun.MK k (P.map Y) < ⊤ → xiEps k ε P X Y κF < ⊤)) ∧
    -- max-functionality
    (OTSensitivity.MaxFun.IsFunctionallyDependent P X Y F →
      xiEps k ε P X Y κF = OTSensitivity.MaxFun.MK k (P.map Y)) ∧
    (OTSensitivity.MaxFun.MK k (P.map Y) < ⊤ →
      xiEps k ε P X Y κF = OTSensitivity.MaxFun.MK k (P.map Y) →
      OTSensitivity.MaxFun.IsFunctionallyDependent P X Y F) ∧
    -- Theorem 8 for ξ^{K_ε}: (23)
    xiEps k ε P X Y κF ≤ xiEps k ε P X Y κ ∧
    -- Theorem 8 for ξ^{K_ε}: (24) and the injective case
    (xiEps k ε P (g ∘ X) Y κU ≤ xiEps k ε P X Y κ ∧
      xiEps k ε P (g ∘ X) Y κU = xiEps k ε P X Y κg ∧
      (OTSensitivity.Info.IsInjectiveAE (P.map X) g →
        xiEps k ε P X Y κ = xiEps k ε P (g ∘ X) Y κU)) ∧
    -- Theorem 9 for ξ^{K_ε}: (25)
    Tendsto (fun n => xiEps k ε P X Y (κs n)) atTop (𝓝 (xiEps k ε P X Y κsup)) := by sorry

end OTSensitivity.MaxFun.Supplement
