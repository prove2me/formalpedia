-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_potential_jumps
-- name    : MLAMaxDelay.RandomizedTimer.potential_jumps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:31.798228+00:00
-- url     : https://prove2.me/theorems/83b76953-6a73-4c18-ad8a-8cef61385539
-- title:
--   Lemma 5.1 — potential limits and nonnegative jumps
-- statement:
--   Fix a nonempty input (the timer potential $Q$ is computed on its zero-path preprocessing). At every interior breakpoint $z$, the genuine one-sided limits of the actual timer potential exist, and
--   $$Q(z^-)\le Q(z^+).$$
--   The quantifier includes coincident acceptance equalities and simultaneous block merges. Limit existence is explicit; no claim of continuity or equality is imposed.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
--   - encoding: fixed nonempty input, partitions of the preprocessed epochs, finitely many affine acceptance breakpoints → nonempty original input, Q on the positive reduction, every positive-C interior acceptance equality, with actual one-sided convergence; reason: this is the paper's breakpoint construction, including redundant equality candidates at which the partition does not change; at such a candidate the asserted inequality is equality
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 13, Lemma 5.1, equation (21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential

namespace MLAMaxDelay.RandomizedTimer

/-- Lemma 5.1, p. 13: existence and inequality of actual one-sided limits,
including simultaneous mergers. -/
theorem potential_jumps {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) (hI : I.requests.Nonempty)
    (z : ℝ) (hz : Breakpoint T I z) :
    ∃ qminus qplus : ℝ, HasLeftPotentialLimit T I z qminus ∧
      HasRightPotentialLimit T I z qplus ∧ qminus ≤ qplus := by sorry

end MLAMaxDelay.RandomizedTimer
