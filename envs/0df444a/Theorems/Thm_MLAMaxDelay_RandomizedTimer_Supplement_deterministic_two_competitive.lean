-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_deterministic_two_competitive
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.deterministic_two_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:53:55.010321+00:00
-- url     : https://prove2.me/theorems/f83f5ed8-0974-4cf8-b1e4-06d639e783b8
-- title:
--   Theorem 4.6 — OPT-Timer(1) is 2-competitive on rooted trees
-- statement:
--   Let $T$ be a weighted rooted tree (nonnegative edge weights, at least one positive edge). OPT-Timer(1) — Algorithm 2 with $\theta=1$, including the immediate service of requests whose root path has zero cost — is an online algorithm whose schedule is feasible on every input $I$, and
--
--   $$\mathrm{ALG}(I)\le 2\,\mathrm{OPT}(I)\qquad\text{for every input } I,$$
--
--   with no additive constant. Here $\mathrm{OPT}(I)$ is the genuine offline optimum over all feasible schedules. Together with Theorem A.2 this shows that 2 is the optimal deterministic competitive ratio on every rooted tree.
--
--   Differences from the source:
--   - encoding: finite rooted tree with nonnegative edge weights and at least one positive edge (Section 2 standing assumption) → the published WeightedTree (parent map, nonnegative non-root weights, a positive edge); reason: the base mission's moderated model; every source tree is represented
--   - encoding: finite labelled request occurrences → a Finset of natural-number labels with arrival and location maps (published Input); reason: every finite labelled input admits an injective relabelling; simultaneous arrivals and repeated locations are kept
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: OPT-Timer(1) is 2-competitive → Causal (fun I => optTimer T I 1) ∧ ∀ I, Feasible T I (optTimer T I 1) ∧ cost ≤ 2 · optimum; reason: Section 2's strictly multiplicative definition; online-ness and feasibility are what Algorithm 2 ensures and are stated rather than assumed
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 12, Theorem 4.6 and its proof; p. 8, Algorithm 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Timer

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Theorem 4.6, p. 12: the actual OPT-Timer(1) execution (zero-path preprocessing included)
is online, feasible, and strictly 2-competitive against the genuine offline optimum, on every
weighted rooted tree and every input. -/
theorem deterministic_two_competitive {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) :
    Causal (fun I => optTimer T I 1) ∧
    ∀ I : Input V, Feasible T I (optTimer T I 1) ∧
      cost T I (optTimer T I 1) ≤ 2 * optimum T I := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
