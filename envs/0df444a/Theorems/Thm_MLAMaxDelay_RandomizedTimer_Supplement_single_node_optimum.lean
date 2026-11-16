-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_single_node_optimum
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.single_node_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:56:51.873875+00:00
-- url     : https://prove2.me/theorems/59cea502-c200-4b29-b03d-4de085ba455d
-- title:
--   Lemma A.1 — offline optimum when all requests lie at one node
-- statement:
--   Let $T$ be a weighted rooted tree and $v$ a vertex whose root path has weight $c=w(P(\rho,v))>0$. Let $I$ be an input whose requests all lie at $v$, with $N\ge1$ distinct arrival times $a_1<\dots<a_N$ (several requests may share a time), and $g_i=a_{i+1}-a_i$. Then
--
--   $$\mathrm{OPT}(I)=c+\sum_{i=1}^{N-1}\min\{g_i,c\}.\qquad(26)$$
--
--   This exact formula is the offline benchmark of both lower-bound constructions in Appendix A.
--
--   Differences from the source:
--   - encoding: finite rooted tree with nonnegative edge weights and at least one positive edge (Section 2 standing assumption) → the published WeightedTree (parent map, nonnegative non-root weights, a positive edge); reason: the base mission's moderated model; every source tree is represented
--   - encoding: finite labelled request occurrences → a Finset of natural-number labels with arrival and location maps (published Input); reason: every finite labelled input admits an injective relabelling; simultaneous arrivals and repeated locations are kept
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: one-based closed epoch intervals R[i,j] with a_1 < ⋯ < a_n → zero-based half-open intervals [i−1, j) of the sorted epoch list; reason: an index shift that avoids truncated subtraction; every interval of the source is represented
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 18, Lemma A.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_LowerBound

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Lemma A.1, p. 18, equation (26). Several requests may share an arrival time: the formula is
over the `N ≥ 1` distinct arrival times `a₁ < ⋯ < a_N` (zero-based `epochTime I 0, …`). -/
theorem single_node_optimum {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (v : V) (hc : 0 < pathCost T v) (I : Input V)
    (hI : I.requests.Nonempty) (hv : ∀ r ∈ I.requests, I.location r = v) :
    optimum T I = ENNReal.ofReal (pathCost T v +
      ∑ i ∈ Finset.range ((epochs I).length - 1),
        min (epochTime I (i + 1) - epochTime I i) (pathCost T v)) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
