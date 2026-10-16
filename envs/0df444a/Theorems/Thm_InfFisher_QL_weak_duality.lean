-- Prove2me | Theorems.Thm_InfFisher_QL_weak_duality
-- name    : InfFisher.QL.weak_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:18.651643+00:00
-- url     : https://prove2.me/theorems/791b854e-5a91-452c-8060-a5677ad9387d
-- title:
--   (A.15), pp. a21–a22 — weak duality
-- statement:
--   For a quasilinear primal feasible triple $(x,u,\delta)$ with $u_i>0$, and a dual feasible pair $(p,\beta)$ with $\beta_i>0$, weak duality states
--   $$\sum_i(B_i\log u_i-\delta_i)\le\langle p,1\rangle-\sum_iB_i\log\beta_i+\sum_iB_i(\log B_i-1).$$
--
--   This is the terminal inequality of display (A.15), including its exact additive constant. It bounds the primal value by the dual value and supplies the equality conditions used later.
--
--   **Formalization Note** The primal feasibility clauses explicitly include $u_i\le\langle v_i,x_i\rangle+\delta_i$.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 10, (A.15), pp. a21–a22

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem weak_duality
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
      (u δ : Fin n → ℝ), InfFisher.EG.IsAllocation μ x →
      (∀ i, 0 < u i) → (∀ i, 0 ≤ δ i) →
      (∀ i, u i ≤ InfFisher.EG.pair μ (v i) (x i) + δ i) →
      ∀ p β, IsDQLFeasible μ v p β → (∀ i, 0 < β i) →
        (∑ i, (B i * Real.log (u i) - δ i)) ≤
          InfFisher.EG.degObj μ B p β + ∑ i, B i * (Real.log (B i) - 1) := by sorry
end InfFisher.QL
