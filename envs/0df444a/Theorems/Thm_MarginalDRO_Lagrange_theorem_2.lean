-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_theorem_2
-- name    : MarginalDRO.Lagrange.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:08.588361+00:00
-- url     : https://prove2.me/theorems/834dfbc7-ac73-41e4-a833-bb6b1c5276b4
-- title:
--   Theorem 2 (Lagrange Form), p. 14 — max over the Fréchet class of E[max_{x∈𝒳} c̃ᵀx] = max_ν Σ_i max couplings = max_ν inf_ψ L = min_ψ sup_ν L
-- statement:
--   Let $Z(c) := \max_{x\in\mathcal X} c^T x$. Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$, each with finite variance, and let $\mathcal X\subset\mathbb R^n$ be a nonempty finite point set. Write $\Gamma(\mu_1,\dots,\mu_n)$ for the joint laws on $\mathbb R^n$ with marginals $\mu_i$, $\mathcal P(\mathcal X)$ for the probability vectors on $\mathcal X$, $\Pi_i\nu$ for the law of $x_i$ under $\nu$, $\Gamma(\mu_i,\Pi_i\nu)$ for the couplings of $\mu_i$ and $\Pi_i\nu$, and $L$ for the Lagrangian
--   $$L(\{\psi_i\}_{i=1}^n,\nu) = \sum_i\Big(\int\psi_i\,d\Pi_i\nu + \int \max_{x_i\in\mathcal X_i}\{\tilde c_i x_i - \psi_i(x_i)\}\,d\mu_i\Big).$$
--   Then every optimum below is attained and
--   $$\max_{\theta\in\Gamma(\mu_1,\dots,\mu_n)} E_{\tilde c\sim\theta}Z(\tilde c) = \max_{\nu\in\mathcal P(\mathcal X)}\sum_i\max_{\gamma_i\in\Gamma(\mu_i,\Pi_i\nu)} E_{(\tilde c_i,x_i)\sim\gamma_i}\tilde c_i x_i = \max_{\nu\in\mathcal P(\mathcal X)}\ \inf_{\{\psi_i:\mathcal X_i\to\mathbb R\}} L(\{\psi_i\}_i,\nu) \quad\text{(Primal)}$$
--   $$= \min_{\{\psi_i:\mathcal X_i\to\mathbb R\}}\ \sup_{\nu\in\mathcal P(\mathcal X)} L(\{\psi_i\}_i,\nu). \quad\text{(Dual)}$$
--
--   Precisely, there is a real number $v$ such that: (1) the maximum of $E_\theta Z$ over $\theta \in \Gamma(\mu_1,\dots,\mu_n)$ is attained and equals $v$; (2) for every $\nu$ and $i$ the coupling maximum is attained; (3) the maximum over $\nu$ of the sum of coupling maxima is attained and equals $v$; (4) the maximum over $\nu$ of $\inf_\psi L$ is attained and equals $v$; (5) the minimum over $\psi$ of $\sup_\nu L$ is attained and equals $v$.
--
--   The theorem reformulates the worst-case expected optimal value of a linear program with random objective, over all joint laws with given one-dimensional marginals, as a finite-dimensional concave–convex saddle problem over distributions on $\mathcal X$ and univariate prices $\psi_i$ on $\mathcal X_i$.
--
--   **Formalization Note** $\mathcal X$ is a nonempty `Finset` (with $\mathcal X = \emptyset$ the problem has no value); $\mathcal X_i$ is the coordinate projection of $\mathcal X$; $\mathcal P(\mathcal X)$ is the standard simplex. The $\psi_i$ are functions $\mathbb R\to\mathbb R$ of which only the values on $\mathcal X_i$ enter $L$, and $\int\psi_i\,d\Pi_i\nu$ is the finite sum $\sum_x\nu(x)\psi_i(x_i)$. Every max/min is stated with `IsGreatest`/`IsLeast` and every inner inf/sup with `IsGLB`/`IsLUB`, so no default value of a real supremum can decide an equality. In (3) the maximum over $\nu$ of the sum of inner maxima is stated jointly over $(\nu,\gamma_1,\dots,\gamma_n)$, which gives the same number given (2). Finite variance is stated as $\mu_i \in L^2$.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. 14, Theorem 2 (proof pp. ec3–ec5, PDF 51–53)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Theorem 2 (Lagrange Form), p. 14. -/
theorem theorem_2 {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ θ ∈ frechetClass μ, s = ∫ c, Z 𝒳 h𝒳 c ∂θ} v ∧
      (∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i, ∃ m : ℝ,
        IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m) ∧
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳, ∃ γ : Fin n → Measure (ℝ × ℝ),
        (∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) ∧ s = ∑ i, ∫ p, p.1 * p.2 ∂(γ i)} v ∧
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳,
        IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s} v ∧
      IsLeast {s | ∃ ψ : Fin n → ℝ → ℝ,
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s} v := by sorry
end MarginalDRO.Lagrange
