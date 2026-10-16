-- Prove2me | Theorems.Thm_InfFisher_QL_theorem_10
-- name    : InfFisher.QL.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:18.124469+00:00
-- url     : https://prove2.me/theorems/3f5b98fb-9612-4657-8f0e-2a3400300bbf
-- title:
--   Theorem 10, p. 30 — quasilinear Eisenberg–Gale optimality and equilibrium
-- statement:
--   Consider a continuum-item Fisher market on a compact measurable item set $\Theta\subseteq\mathbb R^d$. Each buyer has a nonnegative integrable valuation density $v_i$ with $\int_\Theta v_i>0$ and a budget $B_i>0$. The quasilinear primal and dual Eisenberg–Gale programs satisfy all four conclusions of Theorem 10:
--
--   1. The primal supremum is attained at a pair $(x^*,\delta^*)$ with $x^*$ a pure allocation.
--   2. The dual infimum is attained at $(p^*,\beta^*)$; $\beta^*$ is unique and $p^*=\max_i\beta_i^*v_i$ almost everywhere.
--   3. A feasible primal and dual pair are both optimal exactly when market clearance, $\beta_i(\langle v_i,x_i\rangle+\delta_i)=B_i$, $\delta_i(1-\beta_i)=0$, and $\langle p-\beta_i v_i,x_i\rangle=0$ hold for every buyer.
--   4. An allocation and price form a quasilinear market equilibrium exactly when they extend to an optimal primal and dual pair with that same allocation and price.
--
--   The theorem is the paper's quasilinear counterpart to its linear-utility equilibrium and duality result.
--
--   **Formalization Note** A QLME includes supply feasibility, omitted in the printed definition but required by clause (d). The primal is expressed in $(x,\delta)$ with $u_i=\langle v_i,x_i\rangle+\delta_i$; otherwise clause (c) fails. Positive logarithm arguments represent $\log0=-\infty$, and the KKT utility equation is multiplied out to avoid division by zero.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Theorem 10(a)–(d), p. 30

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem theorem_10
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    (∃ x δ, IsPQLOptimal μ v B x δ ∧ InfFisher.EG.IsPure μ Θ x) ∧
    (∃ p β, IsDQLOptimal μ v B p β ∧
      p =ᵐ[μ] InfFisher.EG.maxScaled v β ∧
      ∀ p' β', IsDQLOptimal μ v B p' β' → β' = β) ∧
    (∀ x δ p β, IsPQLFeasible μ x δ → IsDQLFeasible μ v p β →
      ((IsPQLOptimal μ v B x δ ∧ IsDQLOptimal μ v B p β) ↔
        (InfFisher.EG.pair μ p (fun θ => 1 - ∑ i, x i θ) = 0 ∧
         (∀ i, β i * (InfFisher.EG.pair μ (v i) (x i) + δ i) = B i) ∧
         (∀ i, δ i * (1 - β i) = 0) ∧
         ∀ i, InfFisher.EG.pair μ (fun θ => p θ - β i * v i θ) (x i) = 0))) ∧
    (∀ x p, (∀ i, InfFisher.EG.IsBundle μ (x i)) → InfFisher.EG.IsPrice μ p →
      (IsQLME μ v B x p ↔
        ∃ δ β, IsPQLOptimal μ v B x δ ∧ IsDQLOptimal μ v B p β)) := by sorry
end InfFisher.QL
