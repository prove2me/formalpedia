-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_dual_attained
-- name    : MarginalDRO.Lagrange.proof_thm2_dual_attained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:48.294995+00:00
-- url     : https://prove2.me/theorems/d20125b9-934c-4481-8642-8922ce0060ef
-- title:
--   Proof of Theorem 2, p. ec5 — the infimum over {ψ_i} of sup_ν L({ψ_i},ν) is attained
-- statement:
--   Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$ with finite variance and $\mathcal X\subset\mathbb R^n$ a nonempty finite set. There are functions $\psi^*_1,\dots,\psi^*_n$ such that
--   $$\sup_{\nu\in\mathcal P(\mathcal X)} L(\{\psi^*_i\}_i,\nu) \le \sup_{\nu\in\mathcal P(\mathcal X)} L(\{\psi_i\}_i,\nu) \quad\text{for every family } \{\psi_i\}_i ,$$
--   that is, the dual problem $\inf_{\{\psi_i\}}\sup_\nu L$ has an optimal solution.
--
--   This is the attainment of the "min" in the (Dual) form of Theorem 2.
--
--   **Formalization Note** The supremum over $\nu$ is stated as a least upper bound (`IsLUB`) of the image of the simplex; the minimality of $\psi^*$ is stated against every family $\psi$ and every least upper bound.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. ec5 (PDF 53), proof of Theorem 2 (dual attainment)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Proof of Theorem 2, p. ec5: the infimum of the dual problem is attained. -/
theorem proof_thm2_dual_attained {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ ψstar : Fin n → ℝ → ℝ, ∃ s : ℝ,
      IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψstar ν) '' stdSimplex ℝ 𝒳) s ∧
      ∀ (ψ : Fin n → ℝ → ℝ) (s' : ℝ),
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s' → s ≤ s' := by sorry
end MarginalDRO.Lagrange
