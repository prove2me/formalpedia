-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_deterministic_lower_bound
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.deterministic_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:57:18.991506+00:00
-- url     : https://prove2.me/theorems/e553db6f-3c43-4fb5-bb19-49605f0e5993
-- title:
--   Theorem A.2 — no deterministic online algorithm beats ratio 2
-- statement:
--   Let $T$ be any weighted rooted tree (as in Section 2 it has a positive-weight edge; trees with only one leaf are included). For every deterministic online algorithm $\mathcal A$ — any map from inputs to schedules whose services up to each time $t$ depend only on the requests revealed by $t$, with no feasibility or other assumption — and every $\alpha<2$ there is an input $I$ with
--
--   $$\mathrm{ALG}(I)>\alpha\,\mathrm{OPT}(I).$$
--
--   Thus no deterministic online algorithm has competitive ratio below 2, and Theorem 4.6 is optimal.
--
--   Differences from the source:
--   - encoding: finite rooted tree with nonnegative edge weights and at least one positive edge (Section 2 standing assumption) → the published WeightedTree (parent map, nonnegative non-root weights, a positive edge); reason: the base mission's moderated model; every source tree is represented
--   - encoding: finite labelled request occurrences → a Finset of natural-number labels with arrival and location maps (published Input); reason: every finite labelled input admits an injective relabelling; simultaneous arrivals and repeated locations are kept
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: no deterministic online algorithm has competitive ratio below 2, even if the tree has only one leaf → for every tree, every causal A and every real α < 2, ∃ I with ofReal α · optimum < cost of A I; reason: a ratio below 2 would be some α < 2 with ALG ≤ α·OPT on every input; quantifying over every tree covers the one-leaf trees
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), pp. 18–19, Theorem A.2 and its proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Timer

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Theorem A.2, pp. 18–19: on every weighted rooted tree (the model requires a positive edge;
one-leaf trees are included), every deterministic online algorithm — any causal map from inputs
to schedules, with no feasibility or laziness assumption — fails to be α-competitive for every
α < 2: some input has ALG(I) > α·OPT(I). -/
theorem deterministic_lower_bound {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (A : Input V → Schedule V) (hA : Causal A)
    (α : ℝ) (hα : α < 2) :
    ∃ I : Input V, ENNReal.ofReal α * optimum T I < cost T I (A I) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
