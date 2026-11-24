-- Prove2me | Theorems.Thm_IntConeFPT_equal_block_merge
-- name    : IntConeFPT.equal_block_merge
-- status  : Open
-- author  : @ohnesorgefelix
-- created : 2026-11-24T15:08:06.834537+00:00
-- url     : https://prove2.me/theorems/f070d933-16ac-400b-a05d-55512d6eac33
-- title:
--   Merging two supported generators in one integer fiber
-- statement:
--   Suppose two distinct supported generators of a mixed-integer representation have the same integer block. In a convex set they can be replaced by a single generator at their multiplicity-weighted average. The new representation has strictly smaller support, exactly the same aggregate and count, and the same cost for every cost function of the integer block. Its multiplicity-weighted sum of squared integer coordinates is also unchanged.
-- source:
--   Jansen, Ohnesorge and Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, proof of Lemma 7, pp. 10–11, https://arxiv.org/abs/2609.31328. Local exchange step, not separately numbered.

import Definitions.Def_IntConeFPT_Problem

open IntConeFPT

theorem IntConeFPT.equal_block_merge {d k : ℕ}
    {P : Set ((Fin d → ℝ) × (Fin k → ℝ))} (hP : Convex ℝ P)
    (μ : Gen d k →₀ ℕ) (hs : (↑μ.support : Set _) ⊆ genSet P)
    {a b : Gen d k} (ha : a ∈ μ.support) (hb : b ∈ μ.support)
    (hne : a ≠ b) (hx : a.1 = b.1) :
    ∃ ν : Gen d k →₀ ℕ, (↑ν.support : Set _) ⊆ genSet P ∧
      aggr ν = aggr μ ∧ count ν = count μ ∧
      (∀ f, costOf f ν = costOf f μ) ∧
      (ν.sum fun g n => n * ∑ i, (g.1 i).natAbs ^ 2) =
        (μ.sum fun g n => n * ∑ i, (g.1 i).natAbs ^ 2) ∧
      ν.support.card < μ.support.card := by sorry
