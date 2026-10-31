-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_16
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:13.292178+00:00
-- url     : https://prove2.me/theorems/ed8f4b9a-8969-4247-a5db-eebf0f182584
-- title:
--   Lemma 2.16 — global error estimate of the partition lower bound
-- statement:
--   Let $\alpha+\beta\ge0$, let $\operatorname{supp}\mathbb P_{\tilde\xi}=[a_0,a_2]$ and $a_0<a_1<a_2$. Partition it into $I_1=[a_0,a_1]$ and $I_2=(a_1,a_2]$, with $p_\nu=\mathbb P_{\tilde\xi}(I_\nu)$, conditional means $\mu_{|I_\nu}$, conditional expected SRT functions $\Phi_{|I_\nu}$ and mean $\mu$. Let $\Delta(z)=\Phi(z)-\sum_{\nu=1}^2p_\nu\varphi(z,\mu_{|I_\nu})$. Then for $z\in\operatorname{int}I_\kappa$, $\kappa=1,2$,
--
--   $$
--   0\le\Delta(z)\le\frac12\,p_\kappa(\alpha+\beta)\,\frac{a_\kappa-a_{\kappa-1}}{2},
--   $$
--
--   and $\Delta(z)=0$ for $z\in\{a_0,a_1,a_2\}$.
--
--   Weighting the interval error by its probability gives a global error estimate for the refined lower bound.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: J := supp ℙ_ξ̃ = [a, b] → P.support = Set.Icc a b (Mathlib's support of a measure); reason: the same notion: the set of points every neighbourhood of which has positive probability
--   - encoding: conditional expectations 𝔼_ξ̃[· | ξ ∈ I] and p_ν = ℙ_ξ̃(I_ν) → integrals against the conditional law P[|I] = ℙ(I)⁻¹·P|_I, and P.real I; reason: the elementary conditional expectation given an event of positive probability; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.16, p.234 (PDF 243)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.16 (global error estimate of the partition lower bound).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.16, p.234 (PDF 243),
in the setting of Lemma 2.14. Given the interval partition `{I_ν; ν = 1, 2}` of
`J = supp ℙ_ξ̃` and `z ∈ I_κ`, the global error estimate `Δ(z)` satisfies
`0 ≤ Δ(z) = Φ(z) − Σ_{ν=1}^2 p_ν φ(z, μ_{|I_ν}) ≤ ½ p_κ (α + β)(a_κ − a_{κ−1})/2` for
`z ∈ int I_κ`, whereas for `z ∈ {a₀, a₁, a₂}` we have `Δ(z) = 0`.

**Formalization Note.** `I₁ = [a₀, a₁]`, `I₂ = (a₁, a₂]`, `int I₁ = (a₀, a₁)`,
`int I₂ = (a₁, a₂)`, `p_ν = P.real I_ν`, `μ_{|I_ν} = ∫ ξ dP[|I_ν]`; `hsupp` is
`supp ℙ_ξ̃ = [a₀, a₂]`. The bound keeps the printed form. -/
theorem lemma_2_16 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (a₀ a₁ a₂ : ℝ) (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (hsupp : P.support = Set.Icc a₀ a₂) :
    (∀ z ∈ Set.Ioo a₀ a₁,
      0 ≤ expectedSRT α β γ P z -
          (P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂])) ∧
      expectedSRT α β γ P z -
          (P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂])) ≤
        1 / 2 * P.real (Set.Icc a₀ a₁) * (α + β) * ((a₁ - a₀) / 2)) ∧
    (∀ z ∈ Set.Ioo a₁ a₂,
      0 ≤ expectedSRT α β γ P z -
          (P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂])) ∧
      expectedSRT α β γ P z -
          (P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂])) ≤
        1 / 2 * P.real (Set.Ioc a₁ a₂) * (α + β) * ((a₂ - a₁) / 2)) ∧
    (∀ z ∈ ({a₀, a₁, a₂} : Set ℝ),
      expectedSRT α β γ P z -
          (P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂])) = 0) := by sorry

end KallMayerSLP.SimpleRecourse
