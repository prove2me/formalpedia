-- Prove2me | Theorems.Thm_OnlineCRS_Combine_lemma_2_11
-- name    : OnlineCRS.Combine.lemma_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:02.67609+00:00
-- url     : https://prove2.me/theorems/813b9f4f-a10f-4392-bd18-e3ff9407542f
-- title:
--   Lemma 2.11, p. 15 — the combination is (b, c₁c₂)-selectable
-- statement:
--   Let $P_1,P_2\subseteq[0,1]^N$ be sets of fractional points and let $\mathcal F_1,\mathcal F_2$ be feasible-set predicates. Fix $b,c_1,c_2\in[0,1]$. If two randomized greedy schemes are respectively $(b,c_1)$-selectable for $P_1$ and $(b,c_2)$-selectable for $P_2$, draw their families independently and intersect them. The resulting scheme uses feasible sets from $\mathcal F_1\cap\mathcal F_2$ and satisfies
--
--   $$
--   \Pr[e\text{ is selectable for the combined family at }x]\geq c_1c_2
--   \qquad(x\in b(P_1\cap P_2),\ e\in N).
--   $$
--
--   This supplies the explicit construction behind Theorem 1.9.
--
--   **Formalization Note** The two family distributions are multiplied to encode independent draws. Unit-cube bounds on the input polytopes and the ranges of $b,c_1,c_2$ spell out the paper's standing conventions.
-- source:
--   arXiv:1508.00142v2, Lemma 2.11, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Combination

namespace OnlineCRS.Combine

/-- Lemma 2.11, p. 15: independent intersection of selectable greedy OCRSs. -/
theorem lemma_2_11 {α : Type} [Fintype α] [DecidableEq α]
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
    OnlineCRS.Matroid.IsSelectableRand (fun I => 𝓕₁ I ∧ 𝓕₂ I) (P₁ ∩ P₂)
      b (c₁ * c₂) (combine w₁ w₂) := by sorry

end OnlineCRS.Combine
