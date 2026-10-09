-- Prove2me | Theorems.Thm_OnlineCRS_Combine_combination_ocrs
-- name    : OnlineCRS.Combine.combination_ocrs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:31.930437+00:00
-- url     : https://prove2.me/theorems/952dd27b-32f5-446f-bcf3-c796e6b46f05
-- title:
--   Theorem 1.9, p. 4 — intersecting selectable schemes multiplies selectability
-- statement:
--   Let $P_1,P_2\subseteq[0,1]^N$ be relaxations for feasible families $\mathcal F_1,\mathcal F_2$, and let $b,c_1,c_2\in[0,1]$. Suppose randomized greedy online contention resolution schemes for these relaxations are respectively $(b,c_1)$- and $(b,c_2)$-selectable. Then there exists a randomized greedy scheme for the intersection such that
--
--   $$
--   \Pr[e\text{ is selectable at }x]\geq c_1c_2
--   \qquad\text{for every }x\in b(P_1\cap P_2),\ e\in N.
--   $$
--
--   This closure result lets separate constraints be combined while keeping a quantified selectability guarantee.
--
--   **Formalization Note** The existential witness is a distribution over intersections of independently drawn greedy families. The paper's additional polynomial-time efficiency clause is outside the finite distribution model formalized here.
-- source:
--   arXiv:1508.00142v2, Theorem 1.9, p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Combination

namespace OnlineCRS.Combine

/-- Theorem 1.9, p. 4: the product selectability bound for combined constraints. -/
theorem combination_ocrs {α : Type} [Fintype α] [DecidableEq α]
    (𝓕₁ 𝓕₂ : Finset α → Prop) (P₁ P₂ : Set (α → ℝ))
    (b c₁ c₂ : ℝ)
    (w₁ w₂ : (α → ℝ) → Finset (Finset α) → ℝ)
    (hP₁ : ∀ y ∈ P₁, ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hP₂ : ∀ y ∈ P₂, ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hc₁₀ : 0 ≤ c₁) (hc₁₁ : c₁ ≤ 1)
    (hc₂₀ : 0 ≤ c₂) (hc₂₁ : c₂ ≤ 1)
    (hπ₁ : OnlineCRS.Matroid.IsSelectableRand 𝓕₁ P₁ b c₁ w₁)
    (hπ₂ : OnlineCRS.Matroid.IsSelectableRand 𝓕₂ P₂ b c₂ w₂) :
    ∃ w : (α → ℝ) → Finset (Finset α) → ℝ,
      OnlineCRS.Matroid.IsSelectableRand (fun I => 𝓕₁ I ∧ 𝓕₂ I) (P₁ ∩ P₂) b (c₁ * c₂) w := by sorry

end OnlineCRS.Combine
