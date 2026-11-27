-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_9
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:07:37.413551+00:00
-- url     : https://prove2.me/theorems/a30d1924-847f-4fc0-8fe8-2c122dbecacc
-- title:
--   Theorem 9 — adaptive online spin-block lower bound 2
-- statement:
--   Let $C>0$ and let $A$ be any randomized causal spin-block policy with jointly measurable threshold evaluation on finite histories. Suppose one additive constant compares $A$ with every causal online competitor, uniformly over all bounded-count positive-delay timeout release tests. Then
--   $$c\ge2.$$
--   These tests set a finite timeout and, if a block is observed earlier, release after a strictly positive delay or at the timeout, whichever is earlier. Completed waits reveal only events that occurred. Every algorithm competitive against all adaptive online adversaries satisfies this test comparison.
--
--   Thus the source lower bound holds already for this explicit adversary subclass. Algorithms that never block or have infinite expected blocking times are included; release retains priority at exact threshold equality.
--
--   Differences from the source:
--   - generalization: no factor below 2 against the whole adaptive online adversary class → no factor below 2 even against bounded-count positive-delay timeout tests; reason: the source stop-spinning adversary is realized through finite truncations and arbitrarily small positive delays, so the assertion implies the full adversary lower bound
--   - encoding: release as soon as blocking is observed in the proof → release strictly after observed blocking, capped by a finite timeout; reason: the published base waitCost gives release priority at equality; positive delays avoid charging a block at a release tie
--   - reading: well-defined random interaction costs → jointly measurable finite-history threshold evaluation, and measurable test costs with finite expected comparator cost; reason: no finite expected blocking time, density or support condition is added
--   - encoding: one additive constant for every bounded causal strategy and online B → one constant preceding every N, delayed strategy and causal comparator on the same inputs; reason: arbitrarily many repetitions remain available
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 559, Theorem 9 and governing context

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_adaptiveSpin

namespace NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 9, p.559: lower bound 2, witnessed already by bounded-count
positive-delay timeout tests. This strengthens the source's lower bound by
identifying a sufficient adversary subclass. It repairs the informal proof's
"as soon as" convention using strictly positive delays, while retaining the
published waitCost rule that release wins equality. Infinite times to block and
infinite expected spinning times are permitted. -/
theorem theorem_9 (C : ℝ) (hC : 0 < C)
    (A : NonuniformCompetitive.SpinBlock.RandomizedAlg C) (hreg : SpinRegular A)
    (c : ℝ) (hA : SpinDelayedTestCompetitive A c) : 2 ≤ c := by sorry

end NonuniformCompetitive.Snoopy.Supplement
