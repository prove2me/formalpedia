-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_15
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:20.533368+00:00
-- url     : https://prove2.me/theorems/7f16b1bc-4ad3-4202-a90e-40012fb8e389
-- title:
--   Lemma 2.15 — parameter-free error estimate on each partition interval
-- statement:
--   Let $\alpha+\beta\ge0$, let $\operatorname{supp}\mathbb P_{\tilde\xi}=[a_0,a_2]$ and $a_0<a_1<a_2$. Partition it into $I_1=[a_0,a_1]$ and $I_2=(a_1,a_2]$, with $p_\nu=\mathbb P_{\tilde\xi}(I_\nu)$, conditional means $\mu_{|I_\nu}$, conditional expected SRT functions $\Phi_{|I_\nu}$ and mean $\mu$. For $z\in\operatorname{int}I_\nu$, $\nu=1,2$, the error $\Delta_\nu(z)$ satisfies
--
--   $$
--   0\le\Delta_\nu(z):=\Phi_{|I_\nu}(z)-\varphi(z,\mu_{|I_\nu})\le\frac12(\alpha+\beta)\,\frac{a_\nu-a_{\nu-1}}{2}.
--   $$
--
--   The bound depends only on the cost slopes and the interval length, not on the distribution.
--
--   **Formalization Note** $\operatorname{int}I_1=(a_0,a_1)$ and $\operatorname{int}I_2=(a_1,a_2)$. The bound is kept in the printed form; it equals $(\alpha+\beta)(a_\nu-a_{\nu-1})/4$.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: J := supp ℙ_ξ̃ = [a, b] → P.support = Set.Icc a b (Mathlib's support of a measure); reason: the same notion: the set of points every neighbourhood of which has positive probability
--   - encoding: conditional expectations 𝔼_ξ̃[· | ξ ∈ I] and p_ν = ℙ_ξ̃(I_ν) → integrals against the conditional law P[|I] = ℙ(I)⁻¹·P|_I, and P.real I; reason: the elementary conditional expectation given an event of positive probability; same instances
--   - reading: Δ_ν(z) := Φ_{|I_ν} − φ(z, μ_{|I_ν}) → Φ_{|I_ν}(z) − φ(z, μ_{|I_ν}); reason: the argument z of Φ_{|I_ν} is dropped in print; the proof (p.233) uses Φ_{|I_ν}(z)
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.15, p.232 (PDF 241)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.15 (parameter-free error estimate on each partition interval).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.15, p.232 (PDF 241),
in the setting of Lemma 2.14 (`supp ℙ_ξ̃ = [a₀, a₂]`, `a₀ < a₁ < a₂`, `I₁ = [a₀, a₁]`,
`I₂ = (a₁, a₂]`). For `z ∈ int I_ν`, `ν = 1, 2`, the error estimate `Δ_ν(z)` satisfies
`0 ≤ Δ_ν(z) := Φ_{|I_ν}(z) − φ(z, μ_{|I_ν}) ≤ ½ (α + β) (a_ν − a_{ν−1})/2`.

**Formalization Note.** `int I₁ = (a₀, a₁)`, `int I₂ = (a₁, a₂)`. Conditional quantities as in
Lemma 2.14 (`P[|I_ν]`). The printed `Φ_{|I_ν}` is read as `Φ_{|I_ν}(z)`. The bound is kept in the
printed form `½ (α + β) (a_ν − a_{ν−1})/2` (= `(α + β)(a_ν − a_{ν−1})/4`). -/
theorem lemma_2_15 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (a₀ a₁ a₂ : ℝ) (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (hsupp : P.support = Set.Icc a₀ a₂) :
    (∀ z ∈ Set.Ioo a₀ a₁,
      0 ≤ expectedSRT α β γ P[|Set.Icc a₀ a₁] z - srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) ∧
      expectedSRT α β γ P[|Set.Icc a₀ a₁] z - srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) ≤
        1 / 2 * (α + β) * ((a₁ - a₀) / 2)) ∧
    (∀ z ∈ Set.Ioo a₁ a₂,
      0 ≤ expectedSRT α β γ P[|Set.Ioc a₁ a₂] z - srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ∧
      expectedSRT α β γ P[|Set.Ioc a₁ a₂] z - srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ≤
        1 / 2 * (α + β) * ((a₂ - a₁) / 2)) := by sorry

end KallMayerSLP.SimpleRecourse
