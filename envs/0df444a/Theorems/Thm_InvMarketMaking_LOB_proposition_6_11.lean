-- Prove2me | Theorems.Thm_InvMarketMaking_LOB_proposition_6_11
-- name    : InvMarketMaking.LOB.proposition_6_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:18.682089+00:00
-- url     : https://prove2.me/theorems/f5d9b0d1-a291-4cae-bc51-8ac6789d9e51
-- title:
--   Proposition 6.11 — Algorithm 4 always posts $B_t<A_t$ (corrected: the grids must contain a pair $b<a$)
-- statement:
--   Run Algorithm 4 on finite grids $\mathcal B^\circ,\mathcal A^\circ\subset[0,1]$ that contain a pair $b\in\mathcal B^\circ$, $a\in\mathcal A^\circ$ with $b<a$, and with nonnegative confidence radii. Then for every outcome and every round $t\ge1$:
--
--   1. the candidate pair returned by Algorithm 5 satisfies $B_{t,0}<A_{t,0}$;
--   2. the posted pair satisfies $0\le B_t<A_t\le1$.
--
--   So the algorithm only ever selects feasible actions of the model, whatever the observations and the randomized corrections.
--
--   Differences from the source:
--   - correction: arbitrary finite discretizations B°, A° of [0, 1] (Sec. 6.2) → B°, A° ⊆ [0, 1] finite with some b ∈ B°, a ∈ A°, b < a; reason: counterexample: B° = {9/10}, A° = {1/10} satisfy every assumption of Sec. 6.2, but no grid pair has b < a, so Algorithm 4 posts (9/10, 1/10) in round 1 and B_1 < A_1 fails; the grids (22) of Theorem 6.18 contain 0 < 1
--   - reading: radius functions ψ_t of Notation 6.9 → nonnegative radii (any function of the outcome); reason: every confidence radius is nonnegative; with a negative radius F^up could be negative and the second scan could skip every pair
--   - generalization: B_t < A_t → B_{t,0} < A_{t,0} and 0 ≤ B_t < A_t ≤ 1; reason: the added clauses are steps of the paper's proof and of the model's constraint 0 ≤ B_t < A_t ≤ 1 (p. 14); the source's claim is one conjunct
--   - encoding: Bern(p) draws of Algorithm 4 → 1{U_t < p} with U_t an arbitrary real (the statement holds for every outcome); reason: the conclusion holds for every value of the draw
--   - encoding: Algorithm 5 has no return statement after its second loop (Line 26) → it then returns the outer pair (b_0, a_{M−1}); reason: under this statement's hypotheses (a grid pair b < a, nonnegative radii) the loop always returns (Proposition 6.11), so the fallback is never used
--   - reading: Line 23 of Algorithm 4 updates F̂_t, Ŝ_t on the active sets only → F̂_t(b) = (1/t) Σ_{τ≤t} χ^sell_τ(b) and Ŝ_t(a) = (1/t) Σ_{τ≤t} χ^buy_τ(a) for every price, with F̂_0 = Ŝ_0 = 0; reason: Algorithm 5 evaluates the bounds only on the active sets, which are nested, so the values the algorithm uses are the same
--   - generalization: valuation pairs drawn from the valuation law V of Sec. 3 (supported in [0, 1]², P(V^buy = 1) = P(V^sell = 0) = 0) → arbitrary real valuation sequences (the statement holds for every outcome); reason: the claim is pathwise and does not involve the law of the valuations; the model's outcomes are instances
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Proposition 6.11, p. 41

import Mathlib
import Definitions.Def_InvMarketMaking_LOB_lobRound

open MeasureTheory ProbabilityTheory

namespace InvMarketMaking.LOB

/-- **Proposition 6.11** (corrected; Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 41).
Algorithm 4 always selects a bid-ask pair such that `B_t < A_t`, provided the grids contain a pair
`b < a`. More precisely, for every outcome and every round `t ≥ 1`, the candidate pair of
Algorithm 5 satisfies `B_{t,0} < A_{t,0}`, and the posted pair satisfies `0 ≤ B_t < A_t ≤ 1`.

**Formalization Note** The grids `B°, A°` are finite subsets of `[0,1]` (Definition 4.4, Sec. 6.2)
and the radii are nonnegative (every confidence radius of the paper is). The hypothesis
`∃ b ∈ B°, ∃ a ∈ A°, b < a` is a correction: without it the proposition is false, e.g. for
`B° = {9/10}`, `A° = {1/10}` no grid pair has `b < a` and no posted pair can satisfy `B_t < A_t`.
The grids (22) of Theorem 6.18 satisfy it (`0 < 1`). -/
theorem proposition_6_11 {Ω : Type*} (C : LOBConfig Ω) (M : Market Ω)
    (hB : ↑C.Bg ⊆ Set.Icc (0 : ℝ) 1) (hA : ↑C.Ag ⊆ Set.Icc (0 : ℝ) 1)
    (hfeas : ∃ b ∈ C.Bg, ∃ a ∈ C.Ag, b < a)
    (hψF : ∀ t x ω, 0 ≤ C.ψF t x ω) (hψS : ∀ t x ω, 0 ≤ C.ψS t x ω)
    (t : ℕ) (ht : 1 ≤ t) (ω : Ω) :
    (lobRound C M t ω).bid0 < (lobRound C M t ω).ask0 ∧
    0 ≤ (lobRound C M t ω).bid ∧ (lobRound C M t ω).bid < (lobRound C M t ω).ask ∧
    (lobRound C M t ω).ask ≤ 1 := by sorry

end InvMarketMaking.LOB
