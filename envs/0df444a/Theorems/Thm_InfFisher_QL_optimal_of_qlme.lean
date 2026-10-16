-- Prove2me | Theorems.Thm_InfFisher_QL_optimal_of_qlme
-- name    : InfFisher.QL.optimal_of_qlme
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:28.142319+00:00
-- url     : https://prove2.me/theorems/e29ad97c-ef31-411c-b897-d205211cfa81
-- title:
--   Proof of Theorem 10(d), p. a23 — QLME implies optimality
-- statement:
--   For every quasilinear market equilibrium $(x,p)$, there are nonnegative slack variables $\delta$ and dual utility prices $\beta$ such that $(x,\delta)$ optimizes the quasilinear primal program and the pair with the **same given price** $(p,\beta)$ optimizes the dual.
--
--   This completes the equilibrium characterization of Theorem 10(d).
--
--   **Formalization Note** The price $p$ is the equilibrium price in the hypothesis; it is not replaced by a newly constructed price. The equilibrium predicate includes supply feasibility, which is required for primal feasibility.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 10(d), p. a23

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem optimal_of_qlme
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∀ x p, IsQLME μ v B x p →
      ∃ δ β, IsPQLOptimal μ v B x δ ∧ IsDQLOptimal μ v B p β := by sorry
end InfFisher.QL
