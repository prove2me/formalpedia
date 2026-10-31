-- Prove2me | Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_minimax
-- name    : MarginalDRO.Lagrange.proof_thm2_minimax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:32.923372+00:00
-- url     : https://prove2.me/theorems/baa4088e-9476-4cd0-aba8-d76017b162ee
-- title:
--   Proof of Theorem 2, p. ec5 — partial saddle point: max_ν inf_ψ L(ψ,ν) = inf_ψ sup_ν L(ψ,ν)
-- statement:
--   Let $\mu_1,\dots,\mu_n$ be probability measures on $\mathbb R$ with finite variance, $\mathcal X\subset\mathbb R^n$ a nonempty finite set, and $L$ the Lagrangian
--   $$L(\{\psi_i\}_i,\nu) = \sum_{i=1}^n \Big(\int\psi_i\,d\Pi_i\nu + \int \max_{x_i\in\mathcal X_i}\{\tilde c_i x_i - \psi_i(x_i)\}\,d\mu_i\Big).$$
--   Then there is a real number $v$ such that the maximum over $\nu \in \mathcal P(\mathcal X)$ of $\inf_{\{\psi_i\}} L(\{\psi_i\},\nu)$ exists and equals $v$, and $v$ is also the infimum over $\{\psi_i\}$ of $\sup_{\nu\in\mathcal P(\mathcal X)} L(\{\psi_i\},\nu)$:
--   $$\max_{\nu\in\mathcal P(\mathcal X)}\ \inf_{\{\psi_i:\mathcal X_i\to\mathbb R\}} L(\{\psi_i\}_i,\nu) = \inf_{\{\psi_i:\mathcal X_i\to\mathbb R\}}\ \sup_{\nu\in\mathcal P(\mathcal X)} L(\{\psi_i\}_i,\nu).$$
--
--   This exchange of max and inf links the (Primal) and (Dual) forms of Theorem 2.
--
--   **Formalization Note** The functions $\psi_i$ range over all maps $\mathbb R\to\mathbb R$; only their values on $\mathcal X_i$ affect $L$. Inner infima and suprema are stated with `IsGLB`/`IsLUB`, the outer maximum with `IsGreatest`; attainment of the outer infimum is the separate dual-attainment milestone.
-- source:
--   Chen, Ma, Natarajan, Simchi-Levi & Yan, preprint (2018), p. ec5 (PDF 53), proof of Theorem 2 (partial saddle point, Ekeland–Temam Prop. 2.3–Remark 2.3)

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model

open MeasureTheory ProbabilityTheory

namespace MarginalDRO.Lagrange

/-- Proof of Theorem 2, p. ec5: the partial-saddle-point exchange
`max_ν inf_ψ L(ψ, ν) = inf_ψ sup_ν L(ψ, ν)`. -/
theorem proof_thm2_minimax {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳,
        IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s} v ∧
      IsGLB {s | ∃ ψ : Fin n → ℝ → ℝ,
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s} v := by sorry
end MarginalDRO.Lagrange
