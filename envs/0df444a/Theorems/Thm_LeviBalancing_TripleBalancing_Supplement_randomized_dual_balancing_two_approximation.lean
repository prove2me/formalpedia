-- Prove2me | Theorems.Thm_LeviBalancing_TripleBalancing_Supplement_randomized_dual_balancing_two_approximation
-- name    : LeviBalancing.TripleBalancing.Supplement.randomized_dual_balancing_two_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:22:47.430303+00:00
-- url     : https://prove2.me/theorems/ed9754e8-7bcc-4c0c-8fd7-cb39ed9cf246
-- title:
--   Theorem 4.2 (corrected: a finite measurable balancing selector is supplied) — integer-order factor 2
-- statement:
--   Consider the uncapacitated periodic-review model with arbitrary known integer lead time, finite horizon, full backlogging, nonnegative time-dependent transformed rates, real initial inventory and the given nonnegative pipeline. Demands and new orders are integer-valued; future demands may be correlated and nonstationary. Only finite conditional demand means are assumed.
--
--   Let $B$ be the recursively constructed randomized dual-balancing policy of §4.3, with a supplied finite measurable selector of intersections of the integer-cost interpolants at every reached pre-coin state. Its current rounding coin is conditionally independent of demand. For every feasible integer-order policy $P$ whose current action precedes that coin,
--
--   $$
--   E[\mathcal C(B)]\le 2E[\mathcal C(P)].
--   $$
--
--   The same factor holds for the full transformed period cost, including initial unavoidable costs. The statement also certifies that $B$ has feasible nonnegative integer orders. All expected costs are nonnegative extended integrals, so infinite unconditional expectations are retained.
--
--   This gives the source's factor-2 guarantee whenever the integer-order optimum exists. **Formalization Note** No optimality premise is imposed on $P$. The explicit root witness repairs the source's rule-definedness gap; zero holding rates with an unbounded demand tail can leave no finite intersection, as recorded in DISPROOF.md.
--
--   Differences from the source:
--   - correction: a randomized dual-balancing policy is defined for each instance with nonnegative rates → a finite measurable interpolant-root selector is supplied at every reached state; reason: p. 293 claims the holding function grows to infinity; when T=1, L=0, h=0, p=1 and P(D=n)=2^(-n-1), holding is identically zero and expected backlog is positive at every finite order, so no root exists; this excludes precisely runs without a finite measurable root selector, not all zero-rate or unbounded-demand cases (DISPROOF.md)
--   - generalization: comparison with an optimal integer-order policy → comparison with every feasible integer-order policy using pre-coin information; reason: the source comparison proof uses feasibility and nonanticipation only; an optimal policy is included whenever it exists
--   - encoding: conditional joint demand laws and randomized order probabilities → supplied conditional kernels and uniform private coins with distinct pre-coin and post-coin filtrations; reason: the product conditional law implements independent current rounding without imposing demand independence or unconditional integrability
--   - encoding: expected cost in Equation (4) → nonnegative extended integrals for both Equation (4) and the full transformed period cost; reason: infinite unconditional costs remain infinity; the source omits only nonnegative policy-independent initial terms, which preserve the same factor 2
--   - generalization: the policy has the factor-2 cost guarantee → the constructed policy is also proved feasible and integer-valued; reason: these structural conclusions certify that the recursively specified algorithm belongs to the source admissible policy class
-- source:
--   Levi, Pál, Roundy & Shmoys, Approximation Algorithms for Stochastic Inventory Control Models, Math. Oper. Res. 32(2):284–302 (2007), DOI 10.1287/moor.1060.0205, p. 296 (PDF 13), Theorem 4.2; algorithm pp. 295–296 (PDF 12–13); definedness claim p. 293 (PDF 10)

import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Supplement_Randomization

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LeviBalancing.TripleBalancing.Supplement
open LeviBalancing.DualBalancing

/-- Theorem 4.2, pp. 295–296 (PDF 12–13), with the rule-definedness correction explained in
DISPROOF.md: the interpolant intersection must have a finite measurable selector at every
reached state. Zero holding rates and unbounded demands can otherwise leave no intersection.
The comparator is any feasible integer-order policy before the algorithm's CURRENT coin.
The order process itself is constructed, and its admissibility is part of the conclusion. -/
theorem randomized_dual_balancing_two_approximation
    {Ω : Type*} [MeasurableSpace Ω] (I : Instance) (M : RandomizedInput Ω I)
    (r : RootSelector M) (hr : IsBalancingSelector M r)
    (P : ℤ → Ω → ℝ) (hP : IsFeasiblePolicy I M.pre P)
    (hP_integer : ∀ s : ℤ, 1 ≤ s → s ≤ (I.T : ℤ) → ∀ ω, ∃ n : ℕ, P s ω = (n : ℝ)) :
    IsFeasiblePolicy I M.post (randomizedPolicy M r) ∧
    (∀ s : ℤ, 1 ≤ s → s ≤ (I.T : ℤ) → ∀ ω,
      ∃ n : ℕ, randomizedPolicy M r s ω = (n : ℝ)) ∧
    expectedCost I M.μ M.process.D (randomizedPolicy M r) ≤
      2 * expectedCost I M.μ M.process.D P ∧
    expectedFullCost I M.μ M.process.D (randomizedPolicy M r) ≤
      2 * expectedFullCost I M.μ M.process.D P := by sorry

end LeviBalancing.TripleBalancing.Supplement
