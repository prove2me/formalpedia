-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_submodular_offline_structure
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.submodular_offline_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:55:06.292549+00:00
-- url     : https://prove2.me/theorems/0b6e6636-bb6e-4d69-9f61-1dbcec208746
-- title:
--   Lemma 6.2 — offline structure in submodular service-cost models
-- statement:
--   Let a submodular service-cost model (Definition 6.1) and a finite input $I$ with distinct arrival times $a_1<\dots<a_n$ be given; $C(i,j)=\kappa(R[i,j])$ and $D(i,j)$ is the optimum of the subinstance $R[i,j]$, with $D(i,i-1)=0$.
--
--   1. There is an optimal schedule, attaining $\mathrm{OPT}(I)$, whose service batches are the blocks $R[p,q]$ of a partition of the epochs into consecutive blocks, in order, each block $R[p,q]$ served at time $a_q$ by a minimum-cost service object (one that clears $R[p,q]$ at spatial cost $\kappa(R[p,q])$).
--   2. For every $1\le i\le j\le n$,
--   $$D(i,j)=\min_{i\le p\le j}\{D(i,p-1)+C(p,j)+a_j-a_p\}.$$
--   3. For every $1\le i\le j\le n$,
--   $$C(i,j)\le D(i,j)\le C(i,j)+a_j-a_i .$$
--
--   These are the offline facts on which the abstract dynamic program and the timer analysis of Section 6 rest.
--
--   Differences from the source:
--   - encoding: Definition 6.1: a universe U of labelled occurrences, κ on finite sets, service objects → a structure SubmodularModel U Obj over arbitrary types U and Obj, with κ : Finset U → ℝ and the published diminishing-returns submodularity predicate; reason: on finite sets diminishing returns is equivalent to κ(A)+κ(B) ≥ κ(A∪B)+κ(A∩B); nonnegativity follows from κ(∅)=0 and monotonicity
--   - reading: a service object 'has no effect on the availability or cost of later services'; an attaining object 'can be executed at time t ≥ max a(r)' → an object's cleared batch and spatial cost are functions of the object and the current pending set only, and every object can be executed at every time; reason: this is the history independence the definition states; Section 6 imposes no other time restriction
--   - encoding: costs in ℝ with +∞ for an infeasible schedule; OPT the minimum over feasible offline schedules → ℝ≥0∞ costs, ⊤ for infeasible, OPT the infimum over all finite schedules (published cost and optimum); reason: the same values; attainment is part of the base milestones
--   - encoding: one-based closed epoch intervals R[i,j] with a_1 < ⋯ < a_n → zero-based half-open intervals [i−1, j) of the sorted epoch list; reason: an index shift that avoids truncated subtraction; every interval of the source is represented
--   - encoding: a minimum-cost service object for R[p,q] → the serving object clears R[p,q] from R[p,q] at spatial cost κ(R[p,q]), and the actual cleared batch of the k-th service is R[p,q]; reason: this is the attaining object of Definition 6.1, and the batches are read from the actual trace
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 16, Lemma 6.2; p. 15, Definition 6.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_SubmodularModel

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Lemma 6.2, p. 16, all three clauses. Half-open zero-based epoch intervals: source
`R[p,q]` is `[p-1, q)` and source `D(i, p-1)` is `smIntervalD M I i p` (the empty interval
`[i, i)` gives `D = 0`, as a consequence of the definitions). -/
theorem submodular_offline_structure {U Obj : Type} [DecidableEq U]
    (M : SubmodularModel U Obj) (I : Finset U) :
    (∃ S : SMSchedule Obj, ∃ P : List EpochBlock,
      SMFeasible M I S ∧ smCost M I S = smOptimum M I ∧
      PartitionsInterval 0 (smEpochs M I).length P ∧
      (smTrace M I S).length = P.length ∧
      ∀ k : ℕ, k < P.length → ∃ b : EpochBlock, ∃ e : SMService Obj × Finset U × ℝ,
        P[k]? = some b ∧ (smTrace M I S)[k]? = some e ∧
        e.1.1 = smEpochTime M I (b.2 - 1) ∧
        e.2.1 = smIntervalRequests M I b.1 b.2 ∧
        M.clears e.1.2 (smIntervalRequests M I b.1 b.2) = smIntervalRequests M I b.1 b.2 ∧
        M.spatialCost e.1.2 = smIntervalC M I b.1 b.2) ∧
    (∀ i j : ℕ, i < j → j ≤ (smEpochs M I).length →
      smIntervalD M I i j = finiteMinimum i j (fun p =>
        smIntervalD M I i p + smIntervalC M I p j + smEpochTime M I (j - 1) -
          smEpochTime M I p)) ∧
    (∀ i j : ℕ, i < j → j ≤ (smEpochs M I).length →
      smIntervalC M I i j ≤ smIntervalD M I i j ∧
        smIntervalD M I i j ≤ smIntervalC M I i j + smEpochTime M I (j - 1) -
          smEpochTime M I i) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
