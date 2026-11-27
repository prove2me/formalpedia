-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_8
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:07:00.902211+00:00
-- url     : https://prove2.me/theorems/9b5e663c-b045-4ad2-9e71-2ad5e9d8b859
-- title:
--   Theorem 8 — the exact previous-run caching policy is 3-competitive
-- statement:
--   Fix $p\ge1$, a finite block address space, a positive number of processors and arbitrary initial cache states. On each block use $A_p$ for the first write run; thereafter use $A_p$ if the preceding run had length $l\le p$ and $A_0$ if $l>p$. There is a real constant $a$ such that, for every admissible finite input,
--   $$C_{A'}(\sigma)\le3C_{opt}(\sigma)+a.$$
--   The cost and optimum include every block and arbitrary interleavings. This is a pathwise statement, hence also covers inputs selected by adaptive adversaries and comparison against an online competitor whose cost is at least the offline optimum.
--
--   The equality case uses $A_p$, precisely as the rendered source page specifies.
--
--   Differences from the source:
--   - encoding: the specific j = 1 empirical policy → previousRunPolicy uses A_p when l ≤ p, A_0 otherwise, and A_p initially; reason: the tie is visible on PDF p. 17; a fixed first-run choice changes only the additive constant
--   - encoding: 3-competitive against all adversaries → one deterministic pathwise inequality for every admissible family of block projections; reason: a pathwise offline-cost bound implies the corresponding adaptive online and offline comparison bounds
--   - encoding: a fixed unlimited-cache instance → all finite block address spaces and positive processor counts, with arbitrary initial states; reason: projected costs add and every interleaving is represented; the additive constant may depend on the instance
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 558, Theorem 8 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_cacheLearning

namespace NonuniformCompetitive.Snoopy.Supplement

open scoped ENNReal

/-- Theorem 8, p.558: the specified previous-run policy, with the printed l ≤ p
tie. A pathwise bound applies also to adaptively generated inputs. Costs are
summed over every block of an arbitrary fixed finite unlimited-cache instance. -/
theorem theorem_8 (p : ℕ) (hp : 1 ≤ p) (B : Type) [Fintype B] (n : ℕ) (hn : 1 ≤ n)
    (s₀ : B → NonuniformCompetitive.Snoopy.State n) :
    ∃ a : ℝ, ∀ σ : B → List (NonuniformCompetitive.Snoopy.Req n),
      (∀ b, NonuniformCompetitive.Snoopy.Admissible (σ b)) →
      cacheFamilyCost (previousRunPolicy p) s₀ σ ≤
        ENNReal.ofReal (3 * (cacheFamilyOpt p s₀ σ).toReal + a) := by sorry

end NonuniformCompetitive.Snoopy.Supplement
