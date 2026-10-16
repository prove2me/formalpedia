-- Prove2me | Theorems.Thm_InfFisher_QL_A14_attained
-- name    : InfFisher.QL.A14_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:14.305597+00:00
-- url     : https://prove2.me/theorems/13c65a83-be2f-41d6-bbde-168ca6892d8b
-- title:
--   (A.14), p. a21 — the utility-space primal attains its supremum
-- statement:
--   Let $U$ be the attainable utility set of the market. Under the standing compact-item, positive-budget, and positive-integrable-valuation assumptions, the utility-space program
--   $$\sup\left\{\sum_i(B_i\log u_i-\delta_i):u_i>0,\ \delta_i\ge0,\ u-\delta\in U\right\}$$
--   attains its supremum.
--
--   This is the finite-dimensional attainment step used to obtain an optimal pure allocation for the quasilinear primal program.
--
--   **Formalization Note** The domain requires $u_i>0$ to represent the paper's value $\log 0=-\infty$; the relation $u-\delta\in U$ is stated exactly as in (A.14).
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 10(a), (A.14), p. a21

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem A14_attained
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∃ u δ : Fin n → ℝ,
      (∀ i, 0 ≤ δ i) ∧ (∀ i, 0 < u i) ∧
      (fun i => u i - δ i) ∈ InfFisher.EG.feasUtil μ v ∧
      ∀ u' δ' : Fin n → ℝ,
        (∀ i, 0 ≤ δ' i) → (∀ i, 0 < u' i) →
        (fun i => u' i - δ' i) ∈ InfFisher.EG.feasUtil μ v →
        (∑ i, (B i * Real.log (u' i) - δ' i)) ≤
          ∑ i, (B i * Real.log (u i) - δ i) := by sorry
end InfFisher.QL
