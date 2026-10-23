-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_theorem_3
-- name    : MarginalDRO.Lagrange.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:33.278342+00:00
-- url     : https://prove2.me/theorems/9b571270-0dc2-4ae0-b492-f3f2ab4d27b6
-- title:
--   Theorem 3 (Maximization Form), p. 17 — max_θ E Z = max_ν Σ_i max couplings = max_ν of the quantile objective (8), value part
-- statement:
--   Let $\mathcal X \subset \mathbb R^n$ be a nonempty finite set and $\mu_1,\dots,\mu_n$ probability measures on $\mathbb R$ with finite mean. Then there is a real number $v$ such that:
--
--   1. $\max_{\theta\in\Gamma(\mu_1,\dots,\mu_n)} E_{\tilde c\sim\theta} Z(\tilde c)$ is attained and equals $v$;
--   2. for every $\nu \in \mathcal P(\mathcal X)$ and every $i$, $\max_{\gamma_i \in \Gamma(\mu_i,\Pi_i\nu)} E_{\gamma_i}[\tilde c_i x_i]$ is attained;
--   3. $\max_{\nu \in \mathcal P(\mathcal X)} \sum_i \max_{\gamma_i\in\Gamma(\mu_i,\Pi_i\nu)} E_{\gamma_i}[\tilde c_i x_i] = v$ (Primal), attained;
--   4. the concave maximization problem (8) has optimal value $v$, attained:
--   $$v = \max_{\nu \in \mathcal P(\mathcal X)} \sum_{i=1}^n \sum_{x_i \in \mathcal X_i} x_i \int_{\Pi_i\nu((-\infty,x_i - e_i])}^{\Pi_i\nu((-\infty,x_i])} F_{\mu_i}^{-1}(t)\,dt ,$$
--   where $x_i - e_i$ is the largest element of $\mathcal X_i$ below $x_i$ ($-\infty$ if none);
--   5. if $\nu_{\mathrm{rel}}$ solves (8), there is a maximizing joint distribution $\theta^* \in \Gamma(\mu_1,\dots,\mu_n)$, i.e. $E_{\theta^*}Z = v$.
--
--   The quantile form (8) is a finite-dimensional concave program in $\nu$, which is what makes the worst-case expected optimal value computable; it is also the constructive argument for the attainment of the left-hand maximum in Theorem 2.
--
--   **Formalization Note** The page assumes no moment condition; finite means are added so that all expectations are finite. In (2)–(3) the inner maxima are stated as attained for every $\nu$, and the outer maximum is stated jointly over $(\nu,\gamma)$, which gives the same number. The lower limit of (8) is written $\Pi_i\nu((-\infty,x_i))$, equal to $\Pi_i\nu((-\infty,x_i-e_i])$ because $\mathcal X_i$ is finite. Clause 5 is stated as printed; formally it follows from clause 1 (the paper's content is the explicit construction of $\theta^*$ from $\nu_{\mathrm{rel}}$ on pp. ec7–ec8). The further "persistence values" clause of Theorem 3, which needs absolutely continuous marginals, is not part of this statement.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. 17, Theorem 3 (proof pp. ec5–ec9, PDF 53–57)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Theorem 3 (Maximization Form), p. 17, value part. -/
theorem theorem_3 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hint : ∀ i, Integrable id (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ θ ∈ frechetClass μ, s = ∫ c, Z 𝒳 h𝒳 c ∂θ} v ∧
      (∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i, ∃ m : ℝ,
        IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m) ∧
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳, ∃ γ : Fin n → Measure (ℝ × ℝ),
        (∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) ∧ s = ∑ i, ∫ p, p.1 * p.2 ∂(γ i)} v ∧
      IsGreatest ((fun ν => quantileForm μ 𝒳 ν) '' stdSimplex ℝ 𝒳) v ∧
      (∀ νrel ∈ stdSimplex ℝ 𝒳, quantileForm μ 𝒳 νrel = v →
        ∃ θ ∈ frechetClass μ, ∫ c, Z 𝒳 h𝒳 c ∂θ = v) := by sorry
end MarginalDRO.Lagrange
