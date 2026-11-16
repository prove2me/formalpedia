-- Prove2me | Theorems.Thm_MLAMaxDelay_RandomizedTimer_Supplement_theorem_3_3
-- name    : MLAMaxDelay.RandomizedTimer.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:53:07.218439+00:00
-- url     : https://prove2.me/theorems/0a64474e-c19a-4d06-b082-193c5c2f06e7
-- title:
--   Theorem 3.3 — Algorithm 1 runs in polynomial time
-- statement:
--   Let $T$ be a weighted rooted tree on a finite vertex set $V$ and $I$ an input with $N$ request occurrences. Run Algorithm 1 as the explicit step-counted program of the unit-cost arithmetic model (one step per real operation, comparison and finite-structure access; every loop iteration charged). Then
--
--   1. the program returns exactly the value $F(n)=\mathrm{OPT}(I)$ and the schedule computed by the published Algorithm 1;
--   2. there are constants $C,d\in\mathbb N$, independent of $V$, $T$ and $I$, such that its number of steps satisfies
--
--   $$\mathrm{steps}(T,I)\le C\,(N+|V|+1)^d .$$
--
--   Since the explicit tree has $|E|=|V|-1$ edges, $N+|V|$ is the input size up to a constant, so Algorithm 1 runs in time polynomial in the input size. This makes the offline dynamic program, and through it each deadline computation of OPT-Timer, an efficient algorithm rather than only a characterisation of the optimum.
--
--   Differences from the source:
--   - encoding: finite rooted tree with nonnegative edge weights and at least one positive edge (Section 2 standing assumption) → the published WeightedTree (parent map, nonnegative non-root weights, a positive edge); reason: the base mission's moderated model; every source tree is represented
--   - encoding: finite labelled request occurrences → a Finset of natural-number labels with arrival and location maps (published Input); reason: every finite labelled input admits an injective relabelling; simultaneous arrivals and repeated locations are kept
--   - encoding: polynomial time in the input size, in the unit-cost arithmetic model → ∃ C d : ℕ, uniform over every vertex type, tree and input, with tick count ≤ C·(N + |V| + 1)^d for an explicit program on the published tick monad; reason: the input size is N + |E| + O(1) with |E| = |V| − 1; reals are unit cost, so no bit length enters
--   - encoding: Algorithm 1 → offlineProgram, whose returned value and schedule are proved equal to the published offlineAlgorithm; reason: the timed program is tied to the same algorithm whose correctness is the base milestone Theorem 3.2
--   - encoding: sorting the requests in O(N log(N+1)) time (proof of Theorem 3.3) → a charged insertion sort; reason: Algorithm 1 does not fix how line 1 sorts; the theorem asserts only a polynomial bound, which an O(N²) sort still gives
--   - encoding: recovered services represented by their request interval and footprint → backtracking rebuilds each recovered footprint by charged root-path walks; reason: polynomially many extra steps; the returned schedule is the same
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), p. 7, Theorem 3.3 and its proof; p. 5, Algorithm 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_Complexity

namespace MLAMaxDelay.RandomizedTimer.Supplement

/-- Theorem 3.3, p. 7, in the unit-cost arithmetic model of its proof. The step-counted program
`offlineProgram` (Algorithm 1, lines 1–19) returns exactly the published `offlineAlgorithm`'s
value and schedule, and its step count is bounded by a polynomial in the input size
`N + |V|` (the explicit tree has `|E| = |V| − 1` edges), with constants uniform over every
vertex type, every weighted rooted tree and every input. -/
theorem theorem_3_3 :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (T : WeightedTree V) (I : Input V),
      (offlineProgram T I).val =
        ((offlineAlgorithm T I).value, (offlineAlgorithm T I).schedule)) ∧
    ∃ C d : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (T : WeightedTree V) (I : Input V),
      (offlineProgram T I).cost ≤ C * (I.requests.card + Fintype.card V + 1) ^ d := by sorry

end MLAMaxDelay.RandomizedTimer.Supplement
