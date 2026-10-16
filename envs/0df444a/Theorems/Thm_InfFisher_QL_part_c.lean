-- Prove2me | Theorems.Thm_InfFisher_QL_part_c
-- name    : InfFisher.QL.part_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:55.582623+00:00
-- url     : https://prove2.me/theorems/d6fb5aa4-cbe6-4c7d-a5b1-8d708de1e149
-- title:
--   Theorem 10(c), p. 30 — KKT characterization
-- statement:
--   For a feasible primal pair $(x,\delta)$ and dual pair $(p,\beta)$, both are optimal if and only if market clearance and the following conditions hold for every buyer $i$:
--   $$\langle p,1-\sum_jx_j\rangle=0,\qquad \beta_i(\langle v_i,x_i\rangle+\delta_i)=B_i,\qquad \delta_i(1-\beta_i)=0,\qquad \langle p-\beta_i v_i,x_i\rangle=0.$$
--
--   These conditions characterize the matching optimum pair and connect the convex programs to market behavior.
--
--   **Formalization Note** The equation involving $\beta_i$ is multiplied out from $u_i=B_i/\beta_i$, avoiding Lean's total division by zero. The primal variable $u_i$ is defined as $\langle v_i,x_i\rangle+\delta_i$, the saturation required for the converse.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Theorem 10(c), p. 30; proof and (A.16)–(A.19), p. a22

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem part_c
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∀ x δ p β, IsPQLFeasible μ x δ → IsDQLFeasible μ v p β →
      ((IsPQLOptimal μ v B x δ ∧ IsDQLOptimal μ v B p β) ↔
        (InfFisher.EG.pair μ p (fun θ => 1 - ∑ i, x i θ) = 0 ∧
         (∀ i, β i * (InfFisher.EG.pair μ (v i) (x i) + δ i) = B i) ∧
         (∀ i, δ i * (1 - β i) = 0) ∧
         ∀ i, InfFisher.EG.pair μ (fun θ => p θ - β i * v i θ) (x i) = 0)) := by sorry
end InfFisher.QL
