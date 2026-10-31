-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_2
-- name    : MultiUnitProphet.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:31.550426+00:00
-- url     : https://prove2.me/theorems/50b9fda1-1dfa-499a-a182-2169bfaa2bc7
-- title:
--   Lemma 2 — $\phi_k(\boldsymbol\pi,\mathcal F)$ is lowest in the Poisson limit: $\phi_k\le\delta_k(X_\pi)$, with infimum $\phi_k$
-- statement:
--   Let $k\ge1$ and $\lambda_k$ the Poisson rate with $\delta_k(X^{\lambda_k})=\mu_k(X^{\lambda_k})$, $\phi_k=\delta_k(X^{\lambda_k})$.
--
--   1. For every instance $\mathcal F$ (any number of buyers, any arrival order) and every price $\pi$ with $\delta_k(X_\pi)=\mu_k(X_\pi)$,
--   $$\phi_k\ \le\ \phi_k(\boldsymbol\pi,\mathcal F)=\delta_k(X_\pi).$$
--   2. The bound is approached: for every $\eta>0$ there are an atomless instance and a balancing price with $\phi_k(\boldsymbol\pi,\mathcal F)<\phi_k+\eta$.
--
--   So $\phi_k(\boldsymbol\pi,\mathcal F)$ attains its lowest value when $\mathcal F$ is a collection of infinitely many Bernoullis with equal bias, i.e. $X_\pi$ is Poisson. This is the second half of Theorem 1.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - reading: the buyer purchases iff her value is above the price (§2, p.6) → buys iff v_t ≥ p and fewer than k earlier buyers have v_s ≥ p; reason: matches X_p := |{t : v_t ≥ p}| (p.7), which the paper's analysis uses; for atomless laws the tie v_t = p has probability 0
--   - reading: attains its lowest value ϕ_k when F is a collection of infinitely many Bernoulli distributions with equal bias → (1) δ_k(X_π) ≥ φ_k for every instance and balancing price, and (2) instances with δ_k(X_π) < φ_k + η exist for every η > 0; reason: infinitely many buyers are not an instance; the lowest value is the infimum, approached by finite instances
--   - generalization: atomless instances with the scheme's price π(k, F) and n > k → clause (1) for every instance (atoms allowed), every n and every price with δ_k(X_π) = µ_k(X_π); reason: with v_t ≥ p buying, X_π is Poisson-binomial with biases P[v_t ≥ π] for any instance; the paper's setting is a special case
--   - generalization: the WLOG assumption P[v_t > 0] > 0 (§2, p.7) → instances may contain buyers with v_t = 0 almost surely; reason: the Lean statement is true on these instances too, and instances satisfying the WLOG are a special case
--   - encoding: a Poisson random variable X^λ with rate λ → deltaPois k λ = Σ_{j<k} e^{−λ}λ^j/j! and muPois k λ = (1/k) Σ_j min{j,k} e^{−λ}λ^j/j!, with λ : ℝ≥0; reason: the Poisson law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 2, p.8 (proof §5.4, p.16)

import Mathlib
import Definitions.Def_MultiUnitProphet_Model
import Definitions.Def_MultiUnitProphet_Poisson

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 2: the balanced ratio `φ_k(π, F)` is lowest in the Poisson limit.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 2, p.8 (proof §5.4, p.16): "For any supply k and any set of distributions F,
ϕk(π, F) attains its lowest value ϕk(p) when F is a collection of infinitely many Bernoulli
distributions with equal bias, i.e., Xπ(k,F) is a Poisson distribution."

Let `k ≥ 1` and `λ_k` the rate with `δ_k(X^{λ_k}) = µ_k(X^{λ_k})`, `φ_k = δ_k(X^{λ_k})`.
1. For every instance `F` (any number `n` of buyers) and every price `π` with
   `δ_k(X_π) = µ_k(X_π)`: `φ_k ≤ δ_k(X_π) = φ_k(π, F)`.
2. `φ_k` is the infimum: for every `η > 0` some atomless instance and balancing price have
   `φ_k(π, F) < φ_k + η`.

**Formalization Note.** "Attains its lowest value … infinitely many Bernoullis" is read as a lower
bound (1) that is approached by finite instances (2). Clause 1 allows atoms and any balancing
price. -/
theorem lemma_2 (k : ℕ) (hk : 1 ≤ k) (lam : ℝ≥0) (hlam : deltaPois k lam = muPois k lam) :
    (∀ (n : ℕ) (F : Fin n → Measure ℝ), IsInstance F → ∀ p : ℝ, delta k F p = mu k F p →
        deltaPois k lam ≤ delta k F p) ∧
    (∀ η : ℝ, 0 < η → ∃ (n : ℕ) (F : Fin n → Measure ℝ), IsInstance F ∧ (∀ t, NullSingletonClass (F t)) ∧
        ∃ p : ℝ, delta k F p = mu k F p ∧ delta k F p < deltaPois k lam + η) := by sorry

end MultiUnitProphet
