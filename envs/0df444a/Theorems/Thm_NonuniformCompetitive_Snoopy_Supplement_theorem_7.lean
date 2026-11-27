-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_7
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:06:14.377871+00:00
-- url     : https://prove2.me/theorems/d7b0a420-e757-499e-a202-42fc964f6190
-- title:
--   Theorem 7 — a law-independent empirical caching learner attains every larger factor
-- statement:
--   For every integral transfer cost $p\ge1$ there is one deterministic empirical threshold policy $f_p$, independent of all run laws, with the following property. For every fixed finite block address space, every positive number of processors, every initial block-state family and every collection of iid run-length laws $P_b$ on $\mathbb N$,
--   $$\forall c>\frac{e_p}{e_p-1}\ \exists a\in\mathbb R\ \forall (N_b):\qquad
--   \mathbf E C_{f_p}\le c\,\mathbf E C_{opt}+a,\qquad e_p=(1+1/p)^p.$$
--   The expectations use actual causal cache costs on the run inputs. All finite per-block horizons and all valid processor changes are covered. Blocks can have different laws and arbitrary cross-block dependence. The policy minimizes empirical complete-run cost over $A_0,\ldots,A_p$ using all prior runs; its first choice is $A_p$.
--
--   This is an exact every-strict-factor guarantee, with no moment or finite-support assumptions. The additive constant depends on the fixed instance, the laws and $c$, not on the input horizon.
--
--   Differences from the source:
--   - encoding: a fixed unlimited-cache multiprocessor address space with possibly different laws per block → an arbitrary finite block type and sums of the projected block costs; reason: §2 uses finite task systems; all finite address spaces and all interleavings are represented
--   - encoding: independent successive run lengths for each block → every joint input law with iid per-block marginals, and arbitrary adjacent-distinct run owners; reason: cost is invariant under interleaving and renaming active processors, so no cross-block independence is added
--   - encoding: a deterministic adaptive learner obtained from the source mixture → the named empirical minimizer over the mixture support 0 through p, with A_p initially; reason: the finite family already has a member within the source ratio by the averaging argument on p. 557; this fixes an explicit witness without excluding any input law
--   - encoding: c-competitive for all c above e_p/(e_p−1) → the learner is chosen before the instance laws and c, with a before every horizon; reason: this makes distribution independence and the additive-constant quantifiers explicit
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 556, Theorem 7 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_cacheLearning

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Theorem 7, pp.556–557. A single deterministic law-independent per-block
threshold learner works for all iid laws, all strict factors, and every fixed
finite unlimited-cache instance. No moment bound on run lengths is imposed.
All finite address spaces and any interleavings of their runs are covered;
separate blocks need not be independent. -/
theorem theorem_7 (p : ℕ) (hp : 1 ≤ p) :
    ∃ f : CachePolicy p, f = empiricalCachePolicy p ∧ ∀ (B : Type) [Fintype B] (n : ℕ), 1 ≤ n →
      ∀ (s₀ : B → NonuniformCompetitive.Snoopy.State n) (P : B → Measure ℕ),
        (∀ b, IsProbabilityMeasure (P b)) →
        ∀ c : ℝ, NonuniformCompetitive.Snoopy.ep p / (NonuniformCompetitive.Snoopy.ep p - 1) < c →
          CacheIIDCompetitive f s₀ P c := by sorry

end NonuniformCompetitive.Snoopy.Supplement
