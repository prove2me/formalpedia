-- Prove2me | Theorems.Thm_InfFisher_QL_qlme_of_optimal
-- name    : InfFisher.QL.qlme_of_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:23.579247+00:00
-- url     : https://prove2.me/theorems/c0394593-30f4-4029-be93-f7146bc27d18
-- title:
--   Proof of Theorem 10(d), pp. a22–a23 — optimality implies QLME
-- statement:
--   If $(x,\delta)$ optimizes the quasilinear primal program and $(p,\beta)$ optimizes its dual program, then $(x,p)$ is a quasilinear market equilibrium: every buyer maximizes $\langle v_i-p,y\rangle$ among affordable bundles, and the market clears.
--
--   This establishes the forward construction of market equilibrium from the two programs.
--
--   **Formalization Note** Equilibrium includes unit-supply feasibility; this condition is absent from the printed QLME definition but necessary for Theorem 10(d).
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, proof of Theorem 10(d), pp. a22–a23

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

namespace InfFisher.QL

open MeasureTheory

theorem qlme_of_optimal
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∀ x δ p β,
      IsPQLOptimal μ v B x δ → IsDQLOptimal μ v B p β →
      IsQLME μ v B x p := by sorry
end InfFisher.QL
