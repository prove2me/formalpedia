-- Prove2me | Theorems.Thm_MFCLearn_lemma_2_2
-- name    : MFCLearn.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:14.470997+00:00
-- url     : https://prove2.me/theorems/2a6e3f84-88f1-4a41-9ce0-8c4db1917bf2
-- title:
--   Lemma 2.2 — law-invariant property (corrected: $\widehat r$ measurable in $\mu$ for fixed $h$, jointly on countable $\mathcal S$)
-- statement:
--   Assume Outstanding Assumption (A). Fix an admissible control $\pi\in\Pi$ and an initial law $\mu\in\mathcal P(\mathcal S)$, and let $\mu_t$ be the flow (2.10). Then:
--
--   1. for every realization $(s_t,a_t,r_t)$ of the McKean–Vlasov dynamics (2.7) for $(\pi,\mu)$ on any probability space $(\Omega,\mathbb P)$, the random variable $\sum_{t\ge0}\gamma^t r_t$ is integrable, the series $\sum_t\gamma^t\,\widehat r(\mu_t,\pi_t(\mu_t))$ converges, and
--   $$\mathbb E\Big[\sum_{t=0}^\infty\gamma^t r_t\Big]=\sum_{t=0}^\infty\gamma^t\,\widehat r\big(\mu_t,\pi_t(\mu_t)\big);$$
--   so the value depends on the initial state $\xi$ only through its law $\mu$;
--   2. in particular, $v^\pi(\mu)=\sum_{t=0}^\infty\gamma^t\,\widehat r(\mu_t,\pi_t(\mu_t))$ (2.12);
--   3. if $\pi_t(\mu_t)=\delta_{\alpha_t}$ for measurable $\alpha_t:\mathcal S\to\mathcal A$ and every $t$, and $R(s,\mu,a,\nu)=\delta_{r(s,\mu,a,\nu)}$ for some $r:\mathcal S\times\mathcal P(\mathcal S)\times\mathcal A\times\mathcal P(\mathcal A)\to\mathbb R$, then
--   $$v^\pi(\mu)=\sum_{t=0}^\infty\gamma^t\,\widehat r(\mu_t,\delta_{\alpha_t})=\sum_{t=0}^\infty\gamma^t\int_{\mathcal S}r\big(s,\mu_t,\alpha_t(s),\alpha_t\star\mu_t\big)\,\mu_t(ds);$$
--   4. for every $h\in\mathcal H$ the map $\mu\mapsto\widehat r(\mu,h)$ is measurable, and when $\mathcal S$ is countable, $\widehat r$ is jointly measurable on $\mathcal P(\mathcal S)\times\mathcal H$ with the evaluation $\sigma$-algebra on $\mathcal H$.
--
--   With Lemma 2.1, this recasts mean-field control with learning as a control problem on $\mathcal P(\mathcal S)$ with reward $\widehat r$.
--
--   **Formalization Note** The printed lemma calls $\widehat r$ "the measurable function from $\mathcal P(\mathcal S)\times\mathcal H$ to $\mathbb R$"; clause 4 states the measurability that holds.
--
--   Differences from the source:
--
--   - correction: "r̂ is the measurable function from P(S) × H to ℝ" → µ ↦ r̂(µ,h) measurable for each h; r̂ jointly measurable when S is countable, with the evaluation σ-algebra on H; reason: the printed claim is false for uncountable S under every σ-algebra on H: S = [0,1], A = {0,1}, γ = 1/2, P(s,µ,a,ν) = δ_a, R(s,µ,a,ν) = δ_a satisfy every assumption of the source (|r| ≤ 1 gives (A)); for Borel B ⊆ S and h_B(s) = δ₁ if s ∈ B, δ₀ otherwise, Φ(δ_s,h_B)({1}) = r̂(δ_s,h_B) = 1_B(s) and Q(δ_s,h_B) = 1 + 1_B(s), so joint measurability under any σ-algebra Σ on H would make {(s,h_B) : s ∈ B} measurable in Borel(S) ⊗ Σ, which a diagonal argument (Aumann 1961) rules out
--   - generalization: V^π(ξ) for ξ ∈ L(Ω,F,P;S) on the paper's fixed rich atomless Polish probability space → every realization of (2.7) on any probability space, plus the canonical path law (v^π); reason: every process satisfying (2.7) satisfies the clauses of IsRealization, so the paper's processes are instances
--   - generalization: the identity (2.12) V^π(ξ) = Σ_t γ^t r̂(µ_t, π_t(µ_t)) → the identity together with: Σ_t γ^t r_t is integrable and the series Σ_t γ^t r̂(µ_t, π_t(µ_t)) is summable; reason: added conclusions (the paper treats both sides as finite reals under (A), p.6); dropping them gives the printed identity
--   - reading: "h_t = δ_{α_t} for some α_t : S → A" → α_t measurable; reason: δ_{α_t} must lie in H, which consists of measurable maps; Lemma 2.1's strict clause says "measurable function α_t"
--   - reading: (2.7) gives the one-step laws of s_{t+1}, a_t and r_t and leaves the joint conditional law of (r_t, s_{t+1}) given (s_t, a_t) open → the canonical path law draws r_t and s_{t+1} conditionally independently given (s_t, a_t); reason: every expectation in the paper depends only on the laws of (s_t, a_t, r_t), which Lemmas 2.1–2.2 show are the same for every realization of (2.7)
--   - encoding: E^π[Σ_{t=0}^∞ γ^t r(s_t, µ_t, a_t, ν_t)] → Bochner integral of ω ↦ ∑' t, γ^t r_t(ω) under the canonical path law; reason: under (A) the series converges absolutely almost surely and is integrable (Lemma 2.2), so ∑' is the sum of the series and the integral is the expectation
--   - encoding: Outstanding Assumption (A): for any s₀ = ξ ∼ µ, sup_{π∈Π} E^π[Σ_t γ^t |r(s_t, µ_t, a_t, ν_t)|] < ∞ → for every µ, the supremum over controls of the lintegral of Σ_t γ^t |r_t| under the canonical path law is < ⊤; reason: a lintegral of a nonnegative series is the expectation without any integrability side condition; the expectation is the same for every realization of (2.7) (Lemmas 2.1–2.2), and the bound is per µ, as printed
--   - generalization: S, A compact separable metric spaces with their Borel σ-fields; P(X) with W₁ and its Borel σ-field (pp.3–4) → S, A arbitrary measurable spaces; P(X) = ProbabilityMeasure X with the Giry σ-algebra; reason: no metric or compactness is used; the paper identifies the Borel σ-field of P(X) with the σ-field generated by µ ↦ µ(C) (p.3), which is the Giry σ-algebra, so the compact Borel case is an instance
--   - encoding: H = {h : S → P(A) measurable such that Outstanding Assumption (A) holds} (2.9) → H = all Markov kernels S → A (LocalPolicy); reason: (A) is a standing assumption over all of Π and every measurable h is the constant control π_t ≡ h ∈ Π, so the side condition excludes nothing
-- source:
--   Gu, Guo, Wei, Xu, Dynamic Programming Principles for Mean-Field Controls with Learning, arXiv:1911.07314v6, Lemma 2.2, (2.12)–(2.13), p.7

import Mathlib
import Definitions.Def_MFCLearn_Model
import Definitions.Def_MFCLearn_Lifted
import Definitions.Def_MFCLearn_Process

open MeasureTheory ProbabilityTheory

namespace MFCLearn

/-- **Lemma 2.2 (law-invariant property), with the measurability clause corrected.** Gu, Guo, Wei,
Xu, *Dynamic Programming Principles for Mean-Field Controls with Learning*, arXiv:1911.07314v6,
Lemma 2.2, (2.12)–(2.13), p.7. Under Outstanding Assumption (A), for every control `π` and initial
law `μ`, with `μ_t` the flow (2.10):
1. for **every** realization of (2.7) on any probability space, `Σ_t γ^t r_t` is integrable, the
   series `Σ_t γ^t r̂(μ_t, π_t(μ_t))` converges, and `E[Σ_t γ^t r_t] = Σ_t γ^t r̂(μ_t, π_t(μ_t))`; so the
   value depends on the initial state only through its law `μ`;
2. in particular `v^π(μ) = Σ_t γ^t r̂(μ_t, π_t(μ_t))` (2.12);
3. if `π_t(μ_t) = δ_{α_t}` for measurable `α_t : S → A` and `R(s, μ, a, ν) = δ_{r(s, μ, a, ν)}`, then
   `v^π(μ) = Σ_t γ^t r̂(μ_t, δ_{α_t}) = Σ_t γ^t ∫ r(s, μ_t, α_t(s), α_t⋆μ_t) μ_t(ds)`;
4. (corrected) for each `h`, `μ ↦ r̂(μ, h)` is measurable, and for countable `S`, `r̂` is jointly
   measurable on `P(S) × H` with the evaluation σ-algebra on `H`.

**Formalization Note** The printed lemma calls `r̂` "the measurable function from P(S) × H to ℝ";
for uncountable `S` no σ-algebra on `H` makes it jointly measurable, so clause 4 states the
measurability that holds. -/
theorem lemma_2_2 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (m : MFCModel S A) (hA : m.OutstandingA) (π : Control S A) (μ : ProbabilityMeasure S) :
    (∀ (Ω : Type*) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (s : ℕ → Ω → S) (a : ℕ → Ω → A) (r : ℕ → Ω → ℝ),
        m.IsRealization π μ Pr s a r →
        Integrable (fun ω => ∑' t, m.γ ^ t * r t ω) Pr ∧
          Summable (fun t => m.γ ^ t * m.rhat (m.flow π μ t) (π.toLocal t (m.flow π μ t))) ∧
          ∫ ω, ∑' t, m.γ ^ t * r t ω ∂Pr =
            ∑' t, m.γ ^ t * m.rhat (m.flow π μ t) (π.toLocal t (m.flow π μ t))) ∧
      m.vpi π μ = ∑' t, m.γ ^ t * m.rhat (m.flow π μ t) (π.toLocal t (m.flow π μ t)) ∧
      (∀ (α : ℕ → S → A) (hα : ∀ t, Measurable (α t))
        (rf : S × ProbabilityMeasure S × A × ProbabilityMeasure A → ℝ),
        (∀ t, π.toLocal t (m.flow π μ t) = strictPolicy (α t) (hα t)) →
        (∀ x, m.R x = Measure.dirac (rf x)) →
        m.vpi π μ = ∑' t, m.γ ^ t * m.rhat (m.flow π μ t) (strictPolicy (α t) (hα t)) ∧
          m.vpi π μ = ∑' t, m.γ ^ t * ∫ s, rf (s, m.flow π μ t, α t s,
            (m.flow π μ t).map (hα t).aemeasurable) ∂(m.flow π μ t : Measure S)) ∧
      (∀ h : LocalPolicy S A, Measurable (fun μ' : ProbabilityMeasure S => m.rhat μ' h)) ∧
      (Countable S →
        Measurable (fun p : ProbabilityMeasure S × LocalPolicy S A => m.rhat p.1 p.2)) := by sorry

end MFCLearn
