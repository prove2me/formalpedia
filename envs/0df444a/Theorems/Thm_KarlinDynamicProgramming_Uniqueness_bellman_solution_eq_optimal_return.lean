-- Prove2me | Theorems.Thm_KarlinDynamicProgramming_Uniqueness_bellman_solution_eq_optimal_return
-- name    : KarlinDynamicProgramming.Uniqueness.bellman_solution_eq_optimal_return
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:56:00.924007+00:00
-- url     : https://prove2.me/theorems/070d9f97-797c-4819-b7c8-230092c5b0e6
-- title:
--   Uniqueness under a vanishing signed terminal envelope
-- statement:
--   Let Ω be a Hausdorff state space and D a nonempty compact Hausdorff decision space. Take the stationary nonnegative continuous reward, separately continuous transitions, positive continuous product weights, all infinite strategies, and finite uniform convergence of actual reward partial sums separately at each initial state. If a real M satisfies the attained Bellman equation and its signed terminal envelopes tend to zero at every initial state, then for every ω, M(ω) is the greatest actual infinite-strategy return: every strategy has return at most M(ω), and some strategy attains M(ω). Any other real attained Bellman solution satisfying the same vanishing condition equals M as a function. No existence of an admissible solution is assumed or asserted for every model.
--
--   Differences from the source:
--   - encoding: decisions δ₁, δ₂, …, initial state ω₁, and products through n−1 → decisions s 0, s 1, …, initial state trajectory 0, and product over j < N with N = n−1 for the terminal expression; reason: a bijective shift of indices preserves every trajectory, reward and terminal value; the unused last source decision is harmless because D is nonempty
--   - encoding: attained maxima written as max → IsGreatest of the actual range, with existential inner maximum functions in the two-step display; reason: membership asserts attainment and the upper-bound clause asserts dominance over every allowed decision or strategy
--   - encoding: finite real reward series converging uniformly over strategies for each initial state → real tsum of actual stage returns and an epsilon definition of finite uniform convergence of actual partial sums; reason: uniform convergence implies convergence along each strategy and hence summability, excluding the real tsum default on nonsummable inputs
--   - generalization: vanishing attained signed terminal maxima → vanishing finite real least upper bounds of signed terminal ranges; reason: an attained real maximum is its least upper bound, so every source instance satisfies this condition; Bellman and optimal-payoff attainment remain required
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Research Logistics Quarterly 2(4) (1955), 285–294, doi:10.1002/nav.3800020408; Uniqueness, Therefore display together with the following zero-limit paragraph, PDF 6–7 / printed 290–291

import Definitions.Def_KarlinDynamicProgramming_Uniqueness_CandidateSolutions

namespace KarlinDynamicProgramming.Uniqueness

/-- Uniqueness, Therefore display WITH the following zero-limit condition,
printed pp. 290–291 (PDF 6–7). The terminal-envelope condition extends terminal
maxima to finite least upper bounds; payoff and Bellman maxima remain attained. -/
theorem bellman_solution_eq_optimal_return
    {Ω D : Type*} [TopologicalSpace Ω] [T2Space Ω]
    [TopologicalSpace D] [T2Space D] [CompactSpace D] [Nonempty D]
    (m : Model Ω D) (hreturns : UniformFiniteReturns m)
    (M : Ω → ℝ) (hM : Admissible m M) :
    (∀ ω, IsGreatest (Set.range (totalReturn m ω)) (M ω)) ∧
    (∀ M' : Ω → ℝ, Admissible m M' → M = M') := by sorry

end KarlinDynamicProgramming.Uniqueness
