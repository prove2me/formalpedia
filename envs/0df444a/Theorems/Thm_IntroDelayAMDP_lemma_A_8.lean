-- Prove2me | Theorems.Thm_IntroDelayAMDP_lemma_A_8
-- name    : IntroDelayAMDP.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:46.921362+00:00
-- url     : https://prove2.me/theorems/13fc6d55-189a-46d8-90f7-068726b832b0
-- title:
--   Lemma A.8 — concentration of the numbers of attempts
-- statement:
--   In the abstract setting of p.34: in every episode $\kappa$ the indices $i$ that attempt are fixed given $\mathcal F_{\kappa-1}$; given $\mathcal F_{\kappa-1}$ and $\tau_\kappa$ the indicators $I_{i,\kappa}$ are independent with means $\gamma+(1-\gamma)\bar\alpha_{i,\kappa}$, where $\bar\alpha_{i,\kappa}\in[0,1]$, at most $\nu H$ of them are positive, and $\mathbb E[\gamma+(1-\gamma)\bar\alpha_{i,\kappa}\mid\mathcal F_{\kappa-1}]=p_i>0$; the weights $c_{i,\kappa}\ge0$ are fixed given $\mathcal F_{\kappa-1}$; and $p_i$, $\epsilon_i\in[0,\frac12]$ are fixed when $i$ starts. Let $\lambda>0$ and $\delta'\in(0,1)$.
--
--   1. If $(1+\nu H)\lambda c_{i,\kappa}\le\epsilon_ip_i$ for all $i,\kappa$, then with probability at least $1-\delta'$,
--   $$\sum_\kappa\sum_ic_{i,\kappa}\Bigl(1-\frac{I_{i,\kappa}}{(1-\epsilon_i)p_i}\Bigr)\le\frac{\log(1/\delta')}\lambda.$$
--   2. If $(1+4\nu H)\lambda c_{i,\kappa}\le\epsilon_ip_i$ for all $i,\kappa$, then with probability at least $1-\delta'$,
--   $$\sum_\kappa\sum_ic_{i,\kappa}\Bigl(\frac{I_{i,\kappa}}{(1+\epsilon_i)p_i}-1\Bigr)\le\frac{\log(1/\delta')}\lambda.$$
--
--   It compares weighted numbers of attempts with their means, although estimates attempting in one episode share its trajectory. The paper applies it to several subfamilies of estimates.
--
--   Differences from the source:
--   - encoding: p_i and ϵ_i are fixed when i starts → the functions p_i, ϵ_i do not depend on κ, and on each attempt event they are F_{κ−1}-measurable; reason: the proof conditions only on F_{κ−1} at attempts, and a start precedes all attempts
--   - encoding: the indices that attempt, and sums over i → attempt events att(i, κ) that are F_{κ−1}-measurable, with all conditions and sums over attempts; reason: same instances; the index set is a finite type
--   - encoding: independent given F_{κ−1} and τ_κ → the conditional product formula for every finite set of indices, with 𝒯_κ the σ-algebra of τ_κ, 𝒯_κ ≤ F_κ; reason: the definition of conditional independence for 0-1 variables
--   - reading: means γ + (1 − γ)ᾱ_{i,κ}, γ unspecified → the added hypothesis γ ∈ [0, 1]; reason: a mean of an indicator must be a probability, and γ is the stop probability
--   - encoding: I_{i,κ} the outcome of episode κ's attempt and ᾱ_{i,κ} a quantity given F_{κ−1} and τ_κ → I_{i,κ} is F_κ-measurable and ᾱ_{i,κ} is (F_{κ−1} ∨ σ(τ_κ))-measurable; reason: F_κ contains the history of episode κ, and ᾱ is a function of what is conditioned on
--   - encoding: with probability at least 1 − p → μ(failure set) ≤ p; reason: outer-measure bound on the failure set; no measurability side condition is needed
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Lemma A.8, p.35; setting, p.34

import Mathlib

namespace IntroDelayAMDP

open MeasureTheory

open Classical in
/-- **Lemma A.8 (Concentration of the Numbers of Attempts)** (printed p.35, setting p.34, of Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)).
Setting (p.34): "in every episode `κ`, the indices `i` that make an attempt are fixed given `F_{κ−1}`,
and `I_{i,κ} ∈ {0, 1}` indicates that this attempt succeeds or randomly stops `i`; given `F_{κ−1}` and
`τ_κ`, the indicators `I_{i,κ}` are independent with means `γ + (1 − γ)ᾱ_{i,κ}`, where `ᾱ_{i,κ} ∈ [0, 1]`, at
most `νH` of the `ᾱ_{i,κ}` are positive, and `E[γ + (1 − γ)ᾱ_{i,κ} | F_{κ−1}] = p_i > 0`; the weights
`c_{i,κ} ≥ 0` are fixed given `F_{κ−1}`, and `p_i` and `ϵ_i ∈ [0, ½]` are fixed when `i` starts."
Lemma: "let `λ > 0` and `δ′ ∈ (0, 1)`. (i) If `(1 + νH)λc_{i,κ} ≤ ϵ_i p_i` for all `i` and `κ`, then, with
probability at least `1 − δ′`, `∑_κ ∑_i c_{i,κ}(1 − I_{i,κ}/((1 − ϵ_i)p_i)) ≤ log(1/δ′)/λ`. (ii) If
`(1 + 4νH)λc_{i,κ} ≤ ϵ_i p_i` for all `i` and `κ`, then, with probability at least `1 − δ′`,
`∑_κ ∑_i c_{i,κ}(I_{i,κ}/((1 + ϵ_i)p_i) − 1) ≤ log(1/δ′)/λ`."

**Formalization Note.** Episodes are `κ = 0, …, K − 1`; `ℱ κ` is the information before episode `κ`
(the paper's `F_{κ−1}`), `𝒯 κ` is the σ-algebra of `τ_κ` (known after episode `κ`: `𝒯 κ ≤ ℱ (κ+1)`),
and `I_{i,κ}` is `ℱ (κ+1)`-measurable. The index set of estimates is a finite type; `att i κ` is the
event that `i` attempts in `κ`, and all sums and conditions run over attempts. Independence with the
given means is the product formula for every finite set of indices. "`p_i`, `ϵ_i` fixed when `i`
starts" is encoded as: on each attempt event they are `ℱ κ`-measurable (the proof uses only this). The
means `γ + (1 − γ)ᾱ` being probabilities, `γ ∈ [0, 1]`. -/
theorem lemma_A_8 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (𝒯 : ℕ → MeasurableSpace Ω) (h𝒯 : ∀ κ, 𝒯 κ ≤ ℱ (κ + 1))
    {ι : Type*} [Fintype ι] (K : ℕ) (γ ν H : ℝ) (hγ : 0 ≤ γ ∧ γ ≤ 1)
    (att : ι → ℕ → Set Ω) (hatt : ∀ i κ, MeasurableSet[ℱ κ] (att i κ))
    (I : ι → ℕ → Ω → ℝ) (hI01 : ∀ i κ ω, I i κ ω = 0 ∨ I i κ ω = 1)
    (hIm : ∀ i κ, Measurable[ℱ (κ + 1)] (I i κ))
    (αb : ι → ℕ → Ω → ℝ) (hαm : ∀ i κ, Measurable[ℱ κ ⊔ 𝒯 κ] (αb i κ))
    (hα01 : ∀ i κ ω, 0 ≤ αb i κ ω ∧ αb i κ ω ≤ 1)
    (hαpos : ∀ κ ω,
      ((Finset.univ.filter (fun i => ω ∈ att i κ ∧ 0 < αb i κ ω)).card : ℝ) ≤ ν * H)
    (hind : ∀ κ (J : Finset ι) (b : ι → Bool),
      μ[(⋂ i ∈ J, att i κ).indicator
          (fun ω => ∏ i ∈ J, if b i = true then I i κ ω else 1 - I i κ ω) | ℱ κ ⊔ 𝒯 κ] =ᵐ[μ]
        (⋂ i ∈ J, att i κ).indicator (fun ω => ∏ i ∈ J,
          if b i = true then γ + (1 - γ) * αb i κ ω else 1 - (γ + (1 - γ) * αb i κ ω)))
    (pr : ι → Ω → ℝ) (hp : ∀ i ω, 0 < pr i ω)
    (hmean : ∀ i κ, μ[(att i κ).indicator (fun ω => γ + (1 - γ) * αb i κ ω) | ℱ κ] =ᵐ[μ]
      (att i κ).indicator (pr i))
    (ε : ι → Ω → ℝ) (hε : ∀ i ω, 0 ≤ ε i ω ∧ ε i ω ≤ 1 / 2)
    (hpε : ∀ i κ, Measurable[ℱ κ] ((att i κ).indicator (pr i)) ∧
      Measurable[ℱ κ] ((att i κ).indicator (ε i)))
    (c : ι → ℕ → Ω → ℝ) (hc0 : ∀ i κ ω, 0 ≤ c i κ ω) (hcm : ∀ i κ, Measurable[ℱ κ] (c i κ))
    (lam δ' : ℝ) (hlam : 0 < lam) (hδ : 0 < δ') (hδ1 : δ' < 1) :
    ((∀ i κ ω, ω ∈ att i κ → (1 + ν * H) * lam * c i κ ω ≤ ε i ω * pr i ω) →
      μ {ω | Real.log (1 / δ') / lam < ∑ κ ∈ Finset.range K, ∑ i, (att i κ).indicator
          (fun ω => c i κ ω * (1 - I i κ ω / ((1 - ε i ω) * pr i ω))) ω} ≤ ENNReal.ofReal δ') ∧
    ((∀ i κ ω, ω ∈ att i κ → (1 + 4 * ν * H) * lam * c i κ ω ≤ ε i ω * pr i ω) →
      μ {ω | Real.log (1 / δ') / lam < ∑ κ ∈ Finset.range K, ∑ i, (att i κ).indicator
          (fun ω => c i κ ω * (I i κ ω / ((1 + ε i ω) * pr i ω) - 1)) ω} ≤ ENNReal.ofReal δ') := by sorry

end IntroDelayAMDP
