-- Prove2me | Theorems.Thm_InfFisher_EG_lemma_3_b
-- name    : InfFisher.EG.lemma_3_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:29.64067+00:00
-- url     : https://prove2.me/theorems/2af89192-731f-4872-bba4-7417d3e4f4e5
-- title:
--   Lemma 3(b), p. 9 — optimality exactly matches the three KKT conditions
-- statement:
--   For a feasible primal allocation $x$ and feasible dual pair $(p,\beta)$, both are optimal if and only if the three conditions hold:
--
--   $$\langle p,1-\sum_i x_i\rangle=0,\qquad
--     \beta_i\langle v_i,x_i\rangle=B_i,\qquad
--     \langle p-\beta_iv_i,x_i\rangle=0\quad\text{for every }i.$$
--
--   They express market clearance, the utility to budget relation, and complementary slackness.
--
--   **Formalization Note** The middle condition is multiplied out from the paper's $\langle v_i,x_i\rangle=B_i/\beta_i$ to prevent a zero denominator from acquiring Lean's default value.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma 3(b), (3)–(5), p. 9 (PDF 9)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem lemma_3_b {d n : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i) :
    let μ := volume.restrict Θ
    ∀ x p β, IsAllocation μ x → IsDEGFeasible μ v p β →
      ((IsPEGOptimal μ v B x ∧ IsDEGOptimal μ v B p β) ↔
        pair μ p (fun θ => 1 - ∑ i, x i θ) = 0 ∧
        (∀ i, β i * pair μ (v i) (x i) = B i) ∧
        ∀ i, pair μ (fun θ => p θ - β i * v i θ) (x i) = 0) := by sorry

end InfFisher.EG
