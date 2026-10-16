-- Prove2me | Theorems.Thm_InfFisher_EG_theorem_1
-- name    : InfFisher.EG.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:24.924036+00:00
-- url     : https://prove2.me/theorems/46aff11a-edfd-4ac2-8ade-d3acad481cb7
-- title:
--   Theorem 1, p. 8 — primal and dual attainment and equilibrium equivalence
-- statement:
--   In the continuum Fisher market with compact item space, positive integrable valuations and positive budgets, the primal Eisenberg–Gale program attains its supremum at a pure allocation. The dual program attains its infimum at $(p^*,\beta^*)$, where $\beta^*$ is unique, the optimal price is unique almost everywhere, and
--
--   $$p^*=\max_i\beta_i^*v_i\quad\text{almost everywhere}.$$
--
--   A feasible allocation and price form a market equilibrium exactly when the allocation is primal optimal and the price belongs to an optimal dual pair. This is the paper's central existence and characterization theorem.
--
--   **Formalization Note** Prices and pure allocations are compared almost everywhere. Program optimality uses positive utilities and multipliers to represent the source's infinite logarithmic objective at zero.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Theorem 1(a)–(c), p. 8 (PDF 8)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem theorem_1 {d n : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i) :
    let μ := volume.restrict Θ
    (∃ x, IsPEGOptimal μ v B x ∧ IsPure μ Θ x) ∧
    (∃ p β, IsDEGOptimal μ v B p β ∧
      p =ᵐ[μ] maxScaled v β ∧
      ∀ p' β', IsDEGOptimal μ v B p' β' → β' = β ∧ p' =ᵐ[μ] p) ∧
    ∀ x p, (∀ i, IsBundle μ (x i)) → IsPrice μ p →
      (IsME μ v B x p ↔
        IsPEGOptimal μ v B x ∧ ∃ β, IsDEGOptimal μ v B p β) := by sorry

end InfFisher.EG
