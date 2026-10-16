-- Prove2me | Theorems.Thm_InfFisher_EG_theorem_2
-- name    : InfFisher.EG.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:24.862516+00:00
-- url     : https://prove2.me/theorems/209f3c8d-8987-46b3-812d-66da3d6a79bc
-- title:
--   Theorem 2, p. 10 — optimal programs characterize market equilibrium
-- statement:
--   If $x$ optimizes the primal program and $(p,\beta)$ optimizes the dual program, then $(x,p)$ is a market equilibrium and every buyer exhausts its budget and receives utility
--
--   $$\langle p,x_i\rangle=B_i,\qquad
--     \langle v_i,x_i\rangle=B_i/\beta_i.$$
--
--   Conversely, every market equilibrium has a primal optimal allocation and a dual optimal pair whose multiplier is $\beta_i=B_i/\langle v_i,x_i\rangle$. This expands the equivalence in Theorem 1(c).
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Theorem 2, p. 10 (PDF 10)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem theorem_2 {d n : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i) :
    let μ := volume.restrict Θ
    (∀ x p β,
      IsPEGOptimal μ v B x → IsDEGOptimal μ v B p β →
      IsME μ v B x p ∧
      (∀ i, pair μ p (x i) = B i) ∧
      ∀ i, pair μ (v i) (x i) = B i / β i) ∧
    (∀ x p, IsME μ v B x p →
      IsPEGOptimal μ v B x ∧
      IsDEGOptimal μ v B p (fun i => B i / pair μ (v i) (x i))) := by sorry

end InfFisher.EG
