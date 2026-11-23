-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_15
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:08:58.059634+00:00
-- url     : https://prove2.me/theorems/6f5969bc-243b-4ee4-9dd2-c9acb0193d2d
-- title:
--   Theorem 15 — known-coverage normalization on arbitrary metric spaces
-- statement:
--   Let $M$ be any metric space and let $k\ge1$ be a finite server count. Fix an initial configuration $s_0$ and a randomized causal server algorithm $A$ that is $\alpha$-competitive. Then
--   $$\exists A':\quad A'\text{ is }\alpha\text{-competitive from }s_0,\qquad
--   V\subseteq\operatorname{range}(A'(\sigma))\ \text{almost surely whenever KnownCover}(s_0,\sigma,V).$$
--   The known-coverage predicate means that for every target configuration there exists a dominating configuration covering $V$, with the same unordered work function and minimum matching distance as in the appendix. The factor is exactly $\alpha$.
--
--   The assertion includes infinite, unbounded metric spaces and arbitrary finite positive server counts. No global minimum separation or diameter assumption is added.
--
--   Differences from the source:
--   - encoding: general server configurations and cost of moving between them → published labelled path coordinates, the published unordered work function and minimum over server permutations; reason: this gives the unlabelled configuration cost even when servers coincide
--   - encoding: known coverage for every configuration s by some covering s0 → KnownCover uses ∀s ∃t with w(t)+D(t,s) ≤ w(s); reason: the covering configuration depends on the tested configuration, rather than a fixed clairvoyant optimum
--   - encoding: an α-competitive A′ covering known sets → a randomized A′ with the same α and almost-sure coverage after each prefix; reason: the source proof sums over the algorithm distribution, and the request and known set remain universally quantified
--   - encoding: general k-server problems → any metric type and positive finite k, with no global metric bounds; reason: the appendix only uses the finite set visited so far; k = 0 does not define a nonempty service problem
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 569, Theorem 15 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_knownCover

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Theorem 15, Appendix pp.569–570. No finiteness, boundedness or minimum
separation is assumed of M. Permutations are minimized in the work function.
The original mixed-strategy algorithm need not be lazy or phase-based. -/
theorem theorem_15 {M : Type} [MetricSpace M] (k : ℕ) (hk : 0 < k)
    (s₀ : KServer.Config k M) (A : KServer.RandomizedAlgorithm k M) (α : ℝ)
    (hA : A.IsCompetitiveFrom s₀ α) :
    ∃ B : KServer.RandomizedAlgorithm k M,
      B.IsCompetitiveFrom s₀ α ∧
      ∀ (σ : List M) (V : Set M), KnownCover s₀ σ V →
        ∀ᵐ i ∂B.μ, V ⊆ Set.range ((B.alg i).conf σ) := by sorry

end NonuniformCompetitive.Snoopy.Supplement
