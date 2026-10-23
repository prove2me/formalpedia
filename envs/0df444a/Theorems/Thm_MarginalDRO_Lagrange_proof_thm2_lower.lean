-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_lower
-- name    : MarginalDRO.Lagrange.proof_thm2_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:36.275984+00:00
-- url     : https://prove2.me/theorems/c96748cb-76c3-427d-b39f-cedae2f3ff5f
-- title:
--   Proof of Theorem 2, p. ec4 — for every ν and couplings γ_i ∈ Γ(µ_i,Π_iν), some θ ∈ Γ(µ1,…,µn) has E_θ Z ≥ Σ_i E_{γ_i}[c̃_i x_i]
-- statement:
--   Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$ with finite variance and $\mathcal X\subset\mathbb R^n$ a nonempty finite set. For every $\nu \in \mathcal P(\mathcal X)$ and every family of couplings $\gamma_i \in \Gamma(\mu_i,\Pi_i\nu)$, $i = 1,\dots,n$, there is $\theta \in \Gamma(\mu_1,\dots,\mu_n)$ with
--   $$\sum_{i=1}^n E_{(\tilde c_i,x_i)\sim\gamma_i}[\tilde c_i x_i] \le E_{\tilde c\sim\theta}\Big[\max_{x\in\mathcal X}\sum_{i=1}^n \tilde c_i x_i\Big].$$
--   Consequently
--   $$\max_{\theta\in\Gamma(\mu_1,\dots,\mu_n)} E_\theta Z \ge \max_{\nu\in\mathcal P(\mathcal X)} \sum_i \max_{\gamma_i\in\Gamma(\mu_i,\Pi_i\nu)} E_{\gamma_i}[\tilde c_i x_i].$$
--
--   This is the "≥" half of the first equality in Theorem 2.
--
--   **Formalization Note** The page obtains $\theta$ as the $\mathbb R^n$-marginal of the product $\gamma_1\otimes\cdots\otimes\gamma_n$. That construction does not give the inequality in general (the $x$-coordinates of the product are independent and need not form a point of $\mathcal X$; e.g. $\mathcal X = \{(1,0),(0,1)\}$, $\nu$ uniform, $\mu_1=\mu_2$ uniform on $\{0,1\}$), so only the inequality is stated. It holds by gluing the couplings along a common $x\sim\nu$, as in the construction of $\theta^*$ in the proof of Theorem 3.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. ec4 (PDF 52), proof of Theorem 2, first equality (≥)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Proof of Theorem 2, p. ec4: the inequality `max_θ E_θ Z ≥ Σ_i E_{γ_i}[c̃_i x_i]`. -/
theorem proof_thm2_lower {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (ν : 𝒳 → ℝ) (hν : ν ∈ stdSimplex ℝ 𝒳) (γ : Fin n → Measure (ℝ × ℝ))
    (hγ : ∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) :
    ∃ θ ∈ frechetClass μ, ∑ i, ∫ p, p.1 * p.2 ∂(γ i) ≤ ∫ c, Z 𝒳 h𝒳 c ∂θ := by sorry
end MarginalDRO.Lagrange
