-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_6
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:04:26.404311+00:00
-- url     : https://prove2.me/theorems/f2385bbb-5d28-47a6-9f92-c25d688475c3
-- title:
--   Theorem 6 — optimal limited snoopy-cache ratio
-- statement:
--   Fix a limited direct-mapped block snoopy-caching system with at least two processors, positive integral transfer cost $p$, block size $p-1$, any nonempty block-address space (finite or infinite; main memory holds every block not in a cache), finitely many positive cache lines at each processor and arbitrary fixed per-cache hashes. Online and offline algorithms use the same hashes. From every valid initial cache state, both claims hold:
--   $$\forall A,c:\quad A\text{ is }c\text{-competitive against an oblivious adversary}\ \Longrightarrow\ c\ge\frac{e_p}{e_p-1},$$
--   $$\exists A:\quad A\text{ is }\frac{e_p}{e_p-1}\text{-competitive against an oblivious adversary},\qquad e_p=(1+1/p)^p.$$
--   The algorithms are randomized causal control policies, and competitiveness permits one real additive constant independent of the finite input. Dirty evictions, read misses, interleaved runs and the conjunctive empty-line/last-resident snooping restrictions are all included.
--
--   This is the full limited-cache extension, with both optimality claims; it is not a one-block reduction, and it covers every nonempty address space.
--
--   Differences from the source:
--   - encoding: limited block system with fixed per-cache hashes and infinite main memory → arbitrary nonempty B (finite or infinite), per-processor positive finite line counts and fixed hashes shared by all schedules; reason: infinite main memory means memory holds every block not in a cache (p. 554), not that the address set is infinite; nonemptiness supplies the block B of the source
--   - encoding: the limited-model bus and snooping rules → operational fetch/share/privatize/evict controls, resident and last tags, private owners and dirty flags; reason: each snooper must satisfy both numbered conditions; writeback and collision/read costs are charged to every algorithm
--   - reading: every write is preceded by a read to the same block, with the two write-run termination cases → a preparatory read remains valid until another processor accesses that block or this processor accesses a colliding block; reason: pp.550 and 555 require reads at the start of each run; the convention excludes unprepared writes rather than allowing a missing cache copy to be written for free
--   - encoding: the lower bound and attainment at e_p/(e_p−1) → both clauses for n≥2, p≥1 and every valid initial cache state; reason: the positive-transfer and multiprocessor conventions exclude the degenerate undefined-ratio or single-processor cases; initial finite contents only affect the additive constant
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 555, Theorem 6

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_limitedCache

namespace NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 6, p.555, with the full limited direct-mapped cache hardware of
pp.554–556. Each fixed hash is shared by online and offline algorithms. Any
nonempty block-address type is allowed, finite or infinite (main memory holds
every block not in a cache); all interleavings, dirty evictions and the two
conjunctive snooping restrictions are retained. The initial contents are any
valid finite cache state. Positive integral p and at least two processors are
the source's nondegenerate instance conventions. -/
theorem theorem_6 {B : Type} [DecidableEq B] [Nonempty B] (n p : ℕ)
    (hn : 2 ≤ n) (hp : 1 ≤ p) (H : LimitedHardware B n)
    (q₀ : LimitedState H) (hq : LimitedState.Valid H q₀) :
    (∀ (A : LimitedRandomized H p q₀) (c : ℝ),
      A.Competitive c → NonuniformCompetitive.Snoopy.ep p /
        (NonuniformCompetitive.Snoopy.ep p - 1) ≤ c) ∧
    (∃ A : LimitedRandomized H p q₀,
      A.Competitive (NonuniformCompetitive.Snoopy.ep p /
        (NonuniformCompetitive.Snoopy.ep p - 1))) := by sorry

end NonuniformCompetitive.Snoopy.Supplement
