-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_connected_cut_inequalities
-- name    : MLAMaxDelay.RandomizedTimer.connected_cut_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:32.343316+00:00
-- url     : https://prove2.me/theorems/cdc38a0c-11d8-4842-8603-c9eca92c2577
-- title:
--   Lemma 4.4 — extension, cut, and weak-partition inequalities
-- statement:
--   Fix $\theta\in[0,1]$ and $1\le i\le j\le n$. All three source clauses hold:
--
--   1. If $i\le k\le j$ and $[i,k]$ is connected, then
--   $$a_k-a_i+h_\theta(k,j)\le h_\theta(i,j).$$
--   2. If $i<k\le j$, $[i,k-1]$ is connected and $a_k-a_i\ge h_\theta(i,k-1)$, then
--   $$h_\theta(i,k-1)+h_\theta(k,j)\le h_\theta(i,j).$$
--   3. If $B_1,\ldots,B_m$ form a weakly greedy partition of $[i,j]$, then
--   $$\sum_{\ell=1}^m h_\theta(B_\ell)\le h_\theta(i,j).$$
--   These inequalities include weak cut equality and both parameter endpoints. They provide the interval comparison statements for the partition analysis.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: one-based closed epoch interval [i,j] → zero-based half-open interval [i-1,j); reason: the same complete epochs and all source index ranges are preserved; empty intervals have equal endpoints
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 11, Lemma 4.4, equations (8)–(10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential

namespace MLAMaxDelay.RandomizedTimer

/-- Lemma 4.4, p. 11, all three clauses. Half-open endpoints avoid truncated
subtraction at cuts: source [i,k-1] is [i,k) and source [k,j] is [k,j+1). -/
theorem connected_cut_inequalities {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (i j : ℕ) (hij : i < j) (hjn : j ≤ (epochs I).length) :
    (∀ k : ℕ, i ≤ k → k < j → Connected T I θ i (k+1) →
      epochTime I k - epochTime I i + intervalH T I θ k j ≤ intervalH T I θ i j) ∧
    (∀ k : ℕ, i < k → k < j → Connected T I θ i k →
      intervalH T I θ i k ≤ epochTime I k - epochTime I i →
      intervalH T I θ i k + intervalH T I θ k j ≤ intervalH T I θ i j) ∧
    (∀ P : List EpochBlock, WeaklyGreedy T I θ i j P →
      (P.map (fun b => intervalH T I θ b.1 b.2)).sum ≤ intervalH T I θ i j) := by sorry

end MLAMaxDelay.RandomizedTimer
