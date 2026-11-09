-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_busy_block_cost
-- name    : MLAMaxDelay.RandomizedTimer.busy_block_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:43.260981+00:00
-- url     : https://prove2.me/theorems/503f08ba-cc87-422e-85cf-e41c18e92119
-- title:
--   Lemma 4.3 — actual busy-block cost and feasibility
-- statement:
--   For any fixed $\theta\in[0,1]$, each completed busy block $B$ of OPT-Timer has actual cost
--   $$D(B)+\theta C(B).$$
--   The service trace clears exactly that block, its service time is no earlier than its last arrival, and the timer-only schedule is feasible on the positive-path reduction. Its timed blocks agree with the longest-connected-prefix partition and deadlines, with strict nonfinal rejection. These guarantees expose the execution/partition correspondence used by the subsequent inequalities. Zero-path requests remain part of the original-input guarantee in the goal.
--
--   Differences from the source:
--   - encoding: finite undirected rooted tree and nonnegative real edge weights → published rooted parent-map tree with nonroot vertices naming their parent edges; reason: every source tree admits this orientation and every such parent map gives the unique root paths; zero edges and arbitrary finite branching are retained
--   - encoding: finite labelled request occurrences → finite sets of natural-number occurrence labels with arrival and location maps; reason: every finite labelled input admits an injective relabelling; equal times and locations remain distinct
--   - encoding: one-based closed epoch interval [i,j] → zero-based half-open interval [i-1,j); reason: the same complete epochs and all source index ranges are preserved; empty intervals have equal endpoints
--   - encoding: actual schedule minimum, charges defined on nonempty batches, and infinite infeasible cost → ENNReal infimum over finite useful schedules, empty services charged only spatial weight, with toReal for finite-input algebra; reason: there are at most N useful services; empty services can be removed without benefit and do not affect the minimum; Proposition 3.1 explicitly asserts finite attainment, so no default real infimum or infinite toReal is used
--   - encoding: busy blocks of OPT-Timer(θ) on the preprocessed input → timer blocks and timer-only services on the positive-path reduction; reason: zero-path services clear only zero-path requests and cost nothing, so they do not interact with the busy blocks
--   - generalization: total cost of each completed busy block is D(B)+θC(B) → additionally asserts feasibility of the timer schedule, service time ≥ last arrival, the exact cleared batch, equality of the timed blocks with the θ-greedy partition (p. 11) and its strict and weak cuts; reason: extra true conclusions from the proof of Lemma 4.3 and the p. 11 characterization; dropping them gives exactly Lemma 4.3
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 10, Lemma 4.3; event/partition correspondence p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Potential

namespace MLAMaxDelay.RandomizedTimer

/-- Lemma 4.3, p. 10, with its feasibility invariant and the event/greedy
correspondence used on p. 11. Charges are read from the actual service trace. -/
theorem busy_block_cost {V : Type} [Fintype V] [DecidableEq V]
    (T : WeightedTree V) (I : Input V) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let J := positiveInput T I
    let P := timerBlocks T J θ
    Feasible T J (timerServices T J θ) ∧
    (∀ k : ℕ, k < P.length →
      ∃ b : TimedBatch, P[k]? = some b ∧ lastArrival J b.batch ≤ b.time ∧
        ∃ e : Service V × Finset ℕ × ℝ,
          (trace T J (timerServices T J θ))[k]? = some e ∧
          e.2.1 = b.batch ∧ e.2.2 =
            optimumReal T (restrictInput J b.batch) + θ * kappa T J b.batch) ∧
    P = (greedyPartition T J θ).map (fun b =>
      ⟨intervalRequests J b.1 b.2, epochTime J b.1 + intervalH T J θ b.1 b.2⟩) ∧
    WeaklyGreedy T J θ 0 (epochs J).length (greedyPartition T J θ) ∧
    StrictCuts T J θ (greedyPartition T J θ) := by sorry

end MLAMaxDelay.RandomizedTimer
