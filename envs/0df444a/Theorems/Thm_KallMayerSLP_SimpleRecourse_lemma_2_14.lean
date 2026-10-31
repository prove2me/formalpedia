-- Prove2me | Theorems.Thm_KallMayerSLP_SimpleRecourse_lemma_2_14
-- name    : KallMayerSLP.SimpleRecourse.lemma_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:22.303034+00:00
-- url     : https://prove2.me/theorems/f4c8a2a3-abdb-4d8c-9f8f-1ad90399d938
-- title:
--   Lemma 2.14 — the two-interval partition refines Jensen's bound and is exact at the partition points
-- statement:
--   Let $\alpha+\beta\ge0$, let $\operatorname{supp}\mathbb P_{\tilde\xi}=[a_0,a_2]$ and $a_0<a_1<a_2$. Partition it into $I_1=[a_0,a_1]$ and $I_2=(a_1,a_2]$, with $p_\nu=\mathbb P_{\tilde\xi}(I_\nu)$, conditional means $\mu_{|I_\nu}$, conditional expected SRT functions $\Phi_{|I_\nu}$ and mean $\mu$. Then
--
--   1. for every $z\in(a_0,a_2)$
--   $$
--   \varphi(z,\mu)=\varphi(z,p_1\mu_{|I_1}+p_2\mu_{|I_2})\le p_1\varphi(z,\mu_{|I_1})+p_2\varphi(z,\mu_{|I_2})\le p_1\Phi_{|I_1}(z)+p_2\Phi_{|I_2}(z)=\Phi(z);
--   $$
--   2. for every $a_\kappa\in\{a_0,a_1,a_2\}$: $\Phi_{|I_\nu}(a_\kappa)=\varphi(a_\kappa,\mu_{|I_\nu})$ for $\nu=1,2$, and
--   $$
--   \Phi(a_\kappa)=\sum_{\nu=1}^2p_\nu\Phi_{|I_\nu}(a_\kappa)=\sum_{\nu=1}^2p_\nu\varphi(a_\kappa,\mu_{|I_\nu}).
--   $$
--
--   Splitting the support gives a lower bound $\sum_\nu p_\nu\varphi(z,\mu_{|I_\nu})$ that improves on Jensen's and equals $\Phi$ at the partition points.
--
--   Differences from the source:
--   - encoding: a random variable ξ̃ with distribution ℙ_ξ̃ → a probability measure P on ℝ (the law of ξ̃); reason: every quantity in the statement depends on ξ̃ only through its law; same instances
--   - encoding: J := supp ℙ_ξ̃ = [a, b] → P.support = Set.Icc a b (Mathlib's support of a measure); reason: the same notion: the set of points every neighbourhood of which has positive probability
--   - encoding: conditional expectations 𝔼_ξ̃[· | ξ ∈ I] and p_ν = ℙ_ξ̃(I_ν) → integrals against the conditional law P[|I] = ℙ(I)⁻¹·P|_I, and P.real I; reason: the elementary conditional expectation given an event of positive probability; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Lemma 2.14, pp.231–232 (PDF 240–241)

import Mathlib
import Definitions.Def_KallMayerSLP_SimpleRecourse_srt
import Definitions.Def_KallMayerSLP_SimpleRecourse_expectedSRT

open MeasureTheory ProbabilityTheory

namespace KallMayerSLP.SimpleRecourse

/-- **Lemma 2.14 (refining Jensen's bound by a two-interval partition).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Lemma 2.14, pp.231–232
(PDF 240–241). Let `J := supp ℙ_ξ̃ = [a, b]`, partitioned at `a₁ := ẑ ∈ (a, b)` into
`I₁ := [a₀, a₁]` and `I₂ := (a₁, a₂]`, `a₀ := a`, `a₂ := b`, with `p_i := ℙ_ξ̃(I_i)`,
`μ_{|I_i} = 𝔼_ξ̃[ξ̃ | ξ ∈ I_i]`, `Φ_{|I_i}(z) = 𝔼_ξ̃[φ(z, ξ̃) | ξ ∈ I_i]`, `μ = 𝔼_ξ̃[ξ̃]`. Then
a) for arbitrary `z ∈ (a₀, a₂)`:
`φ(z, μ) = φ(z, p₁μ_{|I₁} + p₂μ_{|I₂}) ≤ p₁φ(z, μ_{|I₁}) + p₂φ(z, μ_{|I₂})
≤ p₁Φ_{|I₁}(z) + p₂Φ_{|I₂}(z) = Φ(z)`;
b) for `a_κ ∈ {a₀, a₁, a₂}`: `Φ_{|I_ν}(a_κ) = φ(a_κ, μ_{|I_ν})` for `ν = 1, 2`, and
`Φ(a_κ) = Σ_{ν=1}^2 p_ν Φ_{|I_ν}(a_κ) = Σ_{ν=1}^2 p_ν φ(a_κ, μ_{|I_ν})`.

**Formalization Note.** `P` is the distribution of `ξ̃`; `hsupp` is `supp ℙ_ξ̃ = [a₀, a₂]`
(Mathlib's `Measure.support`), which makes `p₁, p₂ > 0` and `μ` finite. Conditional laws are
`P[|I] = ℙ_ξ̃(I)⁻¹ · P|_I`; `μ_{|I} = ∫ ξ dP[|I]`; `Φ_{|I} = expectedSRT α β γ P[|I]`;
`p_i = P.real I_i`. -/
theorem lemma_2_14 (α β γ : ℝ) (hαβ : 0 ≤ α + β) (P : Measure ℝ) [IsProbabilityMeasure P]
    (a₀ a₁ a₂ : ℝ) (h₀₁ : a₀ < a₁) (h₁₂ : a₁ < a₂) (hsupp : P.support = Set.Icc a₀ a₂) :
    (∀ z ∈ Set.Ioo a₀ a₂,
      srt α β γ z (∫ ξ, ξ ∂P) =
          srt α β γ z (P.real (Set.Icc a₀ a₁) * ∫ ξ, ξ ∂P[|Set.Icc a₀ a₁] +
            P.real (Set.Ioc a₁ a₂) * ∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ∧
      srt α β γ z (P.real (Set.Icc a₀ a₁) * ∫ ξ, ξ ∂P[|Set.Icc a₀ a₁] +
            P.real (Set.Ioc a₁ a₂) * ∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ≤
          P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ∧
      P.real (Set.Icc a₀ a₁) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ z (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ≤
          P.real (Set.Icc a₀ a₁) * expectedSRT α β γ P[|Set.Icc a₀ a₁] z +
            P.real (Set.Ioc a₁ a₂) * expectedSRT α β γ P[|Set.Ioc a₁ a₂] z ∧
      P.real (Set.Icc a₀ a₁) * expectedSRT α β γ P[|Set.Icc a₀ a₁] z +
            P.real (Set.Ioc a₁ a₂) * expectedSRT α β γ P[|Set.Ioc a₁ a₂] z =
          expectedSRT α β γ P z) ∧
    (∀ aκ ∈ ({a₀, a₁, a₂} : Set ℝ),
      expectedSRT α β γ P[|Set.Icc a₀ a₁] aκ = srt α β γ aκ (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) ∧
      expectedSRT α β γ P[|Set.Ioc a₁ a₂] aκ = srt α β γ aκ (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂]) ∧
      expectedSRT α β γ P aκ =
          P.real (Set.Icc a₀ a₁) * expectedSRT α β γ P[|Set.Icc a₀ a₁] aκ +
            P.real (Set.Ioc a₁ a₂) * expectedSRT α β γ P[|Set.Ioc a₁ a₂] aκ ∧
      P.real (Set.Icc a₀ a₁) * expectedSRT α β γ P[|Set.Icc a₀ a₁] aκ +
            P.real (Set.Ioc a₁ a₂) * expectedSRT α β γ P[|Set.Ioc a₁ a₂] aκ =
          P.real (Set.Icc a₀ a₁) * srt α β γ aκ (∫ ξ, ξ ∂P[|Set.Icc a₀ a₁]) +
            P.real (Set.Ioc a₁ a₂) * srt α β γ aκ (∫ ξ, ξ ∂P[|Set.Ioc a₁ a₂])) := by sorry

end KallMayerSLP.SimpleRecourse
