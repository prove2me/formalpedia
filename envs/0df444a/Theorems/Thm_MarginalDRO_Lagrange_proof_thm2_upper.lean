-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_upper
-- name    : MarginalDRO.Lagrange.proof_thm2_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:39.026191+00:00
-- url     : https://prove2.me/theorems/394ac21a-859c-4cad-adcf-ae32f4ce4c64
-- title:
--   Proof of Theorem 2, p. ec4 — with ν := x*#θ and γ_i := (Proj_i, x*_i)#θ ∈ Γ(µ_i,Π_iν), E_θ Z = Σ_i E_{γ_i}[c̃_i x_i]
-- statement:
--   Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$ with finite variance, $\mathcal X\subset\mathbb R^n$ a nonempty finite set, $\theta \in \Gamma(\mu_1,\dots,\mu_n)$, and $x^*:\mathbb R^n\to\mathbb R^n$ a measurable selection of $\arg\max_{x\in\mathcal X} c^Tx$. Define
--   $$\nu(x) := \theta\big(x^* = x\big)\ \ (x \in \mathcal X), \qquad \gamma_i := \text{the law of } (\tilde c_i,\ x^*_i(\tilde c)) \text{ under } \tilde c\sim\theta .$$
--   Then:
--
--   1. $\nu \in \mathcal P(\mathcal X)$;
--   2. $\gamma_i \in \Gamma(\mu_i, \Pi_i\nu)$ for every $i$;
--   3. $$E_{\tilde c\sim\theta}\Big[\max_{x\in\mathcal X}\sum_{i=1}^n \tilde c_i x_i\Big] = \sum_{i=1}^n \int \tilde c_i\, x_i \, d\gamma_i .$$
--
--   Hence $E_\theta Z \le \max_{\nu}\sum_i\max_{\gamma_i} E_{\gamma_i}[\tilde c_i x_i]$: the "≤" half of the first equality in Theorem 2.
--
--   **Formalization Note** $\nu$ and $\gamma_i$ are the push-forwards constructed on the page ($\nu = x^*\#\theta$, $\gamma_i = (\mathrm{Proj}_i, x^*_i)\#\theta$), not existentially quantified objects.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. ec4 (PDF 52), proof of Theorem 2, first equality (≤)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Proof of Theorem 2, p. ec4: with `ν := x*#θ` and `γ_i := (Proj_i, x*_i)#θ`,
`E_θ Z = Σ_i E_{γ_i}[c̃_i x_i]`. -/
theorem proof_thm2_upper {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty)
    (θ : Measure (Fin n → ℝ)) (hθ : θ ∈ frechetClass μ)
    (xstar : (Fin n → ℝ) → (Fin n → ℝ)) (hxm : Measurable xstar)
    (hxmem : ∀ c, xstar c ∈ 𝒳) (hxopt : ∀ c, ∀ x ∈ 𝒳, ∑ i, c i * x i ≤ ∑ i, c i * xstar c i) :
    (fun x : 𝒳 => (θ.map xstar {(x : Fin n → ℝ)}).toReal) ∈ stdSimplex ℝ 𝒳 ∧
      (∀ i, θ.map (fun c => (c i, xstar c i)) ∈
        couplings (μ i) (margMeasure 𝒳 (fun x : 𝒳 => (θ.map xstar {(x : Fin n → ℝ)}).toReal) i)) ∧
      ∫ c, Z 𝒳 h𝒳 c ∂θ = ∑ i, ∫ p, p.1 * p.2 ∂(θ.map (fun c => (c i, xstar c i))) := by sorry
end MarginalDRO.Lagrange
