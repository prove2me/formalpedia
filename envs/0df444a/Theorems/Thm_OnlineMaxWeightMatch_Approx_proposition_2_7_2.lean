-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_proposition_2_7_2
-- name    : OnlineMaxWeightMatch.Approx.proposition_2_7_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:58.514832+00:00
-- url     : https://prove2.me/theorems/7be20220-eb7a-4689-8878-8d7d67a219a7
-- title:
--   Proposition 2.7.2 (NA closure under monotone function composition)
-- statement:
--   Let $X=(X_k)_k$ be a negatively associated family, let $S_1,\dots,S_k$ be pairwise disjoint finite sets of indices, and for each $j$ let $f_j$ be a monotone non-decreasing function of the variables $X_{S_j}=(X_a)_{a\in S_j}$. Then the family
--
--   $$
--   \big(f_1(X_{S_1}),\dots,f_k(X_{S_k})\big)
--   $$
--
--   is negatively associated.
--
--   In the proof of Lemma 4.9 it turns the NA family of pick and coin indicators into the NA family of early-occupancy indicators $O^E_{i,t}=\bigvee_{t'\le t_i}(X_{i,t'}\wedge Y_{i,t'})$.
--
--   **Formalization Note** The functions $f_j$ are taken Borel measurable (so that the $f_j(X_{S_j})$ are random variables); the family of the $f_j$ may be indexed by any type.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 5, Proposition 2.7, part 2

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Proposition 2.7.2 (function composition). If `X` is negatively associated and
`f_1, …, f_k` are monotone non-decreasing (measurable) functions of the coordinates of `X` in
pairwise disjoint index sets `S_1, …, S_k`, then `(f_1(X_{S_1}), …, f_k(X_{S_k}))` is negatively
associated. -/
theorem proposition_2_7_2 {Ω κ ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : κ → Ω → ℝ) (hX : NegativelyAssociated X μ)
    (S : ι → Finset κ) (hS : Pairwise fun j k => Disjoint (S j) (S k))
    (f : (j : ι) → (S j → ℝ) → ℝ) (hmono : ∀ j, Monotone (f j))
    (hmeas : ∀ j, Measurable (f j)) :
    NegativelyAssociated (fun j ω => f j (fun a => X a ω)) μ := by sorry

end OnlineMaxWeightMatch.Approx
