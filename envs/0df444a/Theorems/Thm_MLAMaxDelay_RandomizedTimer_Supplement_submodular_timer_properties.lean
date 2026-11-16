-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_submodular_timer_properties
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.submodular_timer_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:55:42.949053+00:00
-- url     : https://prove2.me/theorems/bfd0708d-98ca-4e52-98b1-112b82c18fea
-- title:
--   Lemma 6.3 — timer and partition properties in submodular service-cost models
-- statement:
--   Fix a submodular service-cost model (Definition 6.1) and an input $I$. For $\theta\in[0,1]$ let $h_\theta=D-(1-\theta)C$, let $P_\theta$ be the partition produced by the abstract OPT-Timer($\theta$) (which is the θ-greedy partition), and $Q(\theta)=\sum_{B\in P_\theta}h_\theta(B)$.
--
--   1. During the execution of OPT-Timer($\theta$), the deadline of an active busy block never moves earlier when a new epoch is accepted; the schedule is feasible, and every completed block $B$ is cleared by one service, at its deadline, of cost
--   $$D(B)+\theta C(B).$$
--   2. For every epoch interval $[i,j]$: (8) if $[i,k]$ is θ-connected ($i\le k\le j$) then $h_\theta(i,j)\ge a_k-a_i+h_\theta(k,j)$; (9) if $[i,k-1]$ is θ-connected and $a_k-a_i\ge h_\theta(i,k-1)$ ($i<k\le j$) then $h_\theta(i,j)\ge h_\theta(i,k-1)+h_\theta(k,j)$; (10) every weakly θ-greedy partition $B_1,\dots,B_m$ of $[i,j]$ satisfies $h_\theta(i,j)\ge\sum_\ell h_\theta(B_\ell)$.
--   3. If $0\le\theta_1\le\theta_2\le1$, every block of $P_{\theta_2}$ is a union of consecutive blocks of $P_{\theta_1}$.
--   4. $P_\theta$ has finitely many interior breakpoints; at every interior breakpoint $z$ both one-sided limits of $Q$ exist and $Q(z^+)\ge Q(z^-)$; the limits $Q(0^+)$ and $Q(1^-)$ exist and
--   $$Q(0^+)\ge 0,\qquad Q(1^-)\le\mathrm{OPT}(I).$$
--
--   These are the online properties from which Theorem 6.4(ii)–(iii) follow.
--
--   Differences from the source:
--   - encoding: Definition 6.1: a universe U of labelled occurrences, κ on finite sets, service objects → a structure SubmodularModel U Obj over arbitrary types U and Obj, with κ : Finset U → ℝ and the published diminishing-returns submodularity predicate; reason: on finite sets diminishing returns is equivalent to κ(A)+κ(B) ≥ κ(A∪B)+κ(A∩B); nonnegativity follows from κ(∅)=0 and monotonicity
--   - reading: a service object 'has no effect on the availability or cost of later services'; an attaining object 'can be executed at time t ≥ max a(r)' → an object's cleared batch and spatial cost are functions of the object and the current pending set only, and every object can be executed at every time; reason: this is the history independence the definition states; Section 6 imposes no other time restriction
--   - encoding: one-based closed epoch intervals R[i,j] with a_1 < ⋯ < a_n → zero-based half-open intervals [i−1, j) of the sorted epoch list; reason: an index shift that avoids truncated subtraction; every interval of the source is represented
--   - encoding: the deadline of an active busy block never moves earlier when a new epoch is accepted → for every intermediate state of the actual execution with active block B, if the next epoch arrives no later than B's deadline then the deadline of B with that epoch added is at least B's deadline; reason: the statement is read along the actual run of Algorithm 2
--   - encoding: P_θ, the partition produced by the abstract OPT-Timer(θ), described on p. 16 as precisely the θ-greedy partition → item (i) concludes that the timer's batches are the greedy blocks, and item (iii) is stated for the greedy partition; reason: the two descriptions of P_θ are proved to agree rather than identified by definition
--   - encoding: breakpoints of P_θ and the values Q(z±) = Σ_{B ∈ P_{z±}} h_z(B) → points of (0,1) at which the timer partition is not locally constant, and genuine one-sided limits of Q; reason: Q is affine in θ on each block, so the source's Q(z±) are exactly these limits
--   - encoding: every completed block B costs D(B) + θC(B) → for every block of the actual run, its service is at its deadline, the deadline is no earlier than the block's last arrival, the cleared batch is B, the charge is D(B) + θC(B), and the whole schedule is feasible; reason: the cost of a block is read from the actual trace, and these are the facts Lemma 4.3's proof (p. 10) establishes along the way; no hypothesis is added
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 16, Lemma 6.3; p. 11, Lemma 4.4; p. 12, Lemma 4.5; pp. 13–14, Lemmas 5.1–5.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_SubmodularTimer

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Lemma 6.3, p. 16, every clause, for the actual abstract OPT-Timer(θ) execution in an
arbitrary submodular service-cost model. Half-open zero-based epoch intervals as in the base
mission: source `[i, k-1]` is `[i, k)` and source `[k, j]` is `[k, j+1)`. -/
theorem submodular_timer_properties {U Obj : Type} [DecidableEq U]
    (M : SubmodularModel U Obj) (I : Finset U) :
    -- (i) deadlines never move earlier on acceptance; every completed block costs D(B) + θC(B);
    -- the timer's batches are the θ-greedy blocks
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      (∀ k : ℕ, k < (smEpochs M I).length → ∀ B : Finset U,
        (smTimerStateAfter M I θ k).active = some B →
        smEpochTime M I k ≤ smDeadline M θ B →
        smDeadline M θ B ≤ smDeadline M θ
          (B ∪ I.filter (fun r => M.arrival r = smEpochTime M I k))) ∧
      SMFeasible M I (smOptTimer M I θ) ∧
      (smTrace M I (smOptTimer M I θ)).length = (smTimerBlocks M I θ).length ∧
      (∀ k : ℕ, k < (smTimerBlocks M I θ).length →
        ∃ b : Finset U × ℝ, ∃ e : SMService Obj × Finset U × ℝ,
          (smTimerBlocks M I θ)[k]? = some b ∧
          (smTrace M I (smOptTimer M I θ))[k]? = some e ∧
          smLastArrival M b.1 ≤ b.2 ∧ e.1.1 = b.2 ∧ e.2.1 = b.1 ∧
          e.2.2 = smOptimumReal M b.1 + θ * M.κ b.1) ∧
      (smTimerBlocks M I θ).map Prod.fst =
        (smGreedyPartition M I θ).map (fun b => smIntervalRequests M I b.1 b.2)) ∧
    -- (ii) inequalities (8), (9), (10)
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ i j : ℕ, i < j → j ≤ (smEpochs M I).length →
      (∀ k : ℕ, i ≤ k → k < j → SMConnected M I θ i (k + 1) →
        smEpochTime M I k - smEpochTime M I i + smIntervalH M I θ k j ≤
          smIntervalH M I θ i j) ∧
      (∀ k : ℕ, i < k → k < j → SMConnected M I θ i k →
        smIntervalH M I θ i k ≤ smEpochTime M I k - smEpochTime M I i →
        smIntervalH M I θ i k + smIntervalH M I θ k j ≤ smIntervalH M I θ i j) ∧
      (∀ P : List EpochBlock, SMWeaklyGreedy M I θ i j P →
        (P.map (fun b => smIntervalH M I θ b.1 b.2)).sum ≤ smIntervalH M I θ i j)) ∧
    -- (iii) nested greedy partitions
    (∀ θ₁ θ₂ : ℝ, 0 ≤ θ₁ → θ₁ ≤ θ₂ → θ₂ ≤ 1 →
      ConsecutiveCoarsening (smGreedyPartition M I θ₁) (smGreedyPartition M I θ₂)) ∧
    -- (iv) finitely many breakpoints, nonnegative jumps, endpoint limits and bounds
    {z : ℝ | SMBreakpoint M I z}.Finite ∧
    (∀ z : ℝ, SMBreakpoint M I z →
      ∃ qminus qplus : ℝ, SMHasLeftPotentialLimit M I z qminus ∧
        SMHasRightPotentialLimit M I z qplus ∧ qminus ≤ qplus) ∧
    (∃ qzero qone : ℝ, SMHasRightPotentialLimit M I 0 qzero ∧
      SMHasLeftPotentialLimit M I 1 qone ∧ 0 ≤ qzero ∧ qone ≤ smOptimumReal M I) := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
