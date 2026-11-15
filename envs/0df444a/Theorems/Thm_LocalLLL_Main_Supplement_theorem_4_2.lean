-- Prove2me | Theorems.Thm_LocalLLL_Main_Supplement_theorem_4_2
-- name    : LocalLLL.Main.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T01:43:48.746768+00:00
-- url     : https://prove2.me/theorems/f7eac7e8-91a5-4d98-a47b-348de96dba60
-- title:
--   Theorem 4.2 — error ε(n) in T(n)·poly(log log(n/ε)) rounds
-- statement:
--   Consider a distributed problem given by a correctness condition on labelled graphs (the condition may refer to the graph, the identifiers, the inputs and the outputs). Suppose that for every size bound $N\ge1$ there is a randomized LOCAL algorithm that, on every graph with at most $N$ nodes and injective identifiers, solves the problem in $T(N)$ rounds with error probability at most $N^{-1000}$, and that on graphs with at most $N$ nodes the output can be checked in $T(N)$ rounds: a deterministic $T(N)$-round checker accepts at every node exactly when the output is correct.
--
--   Then there are absolute constants $A>0$ and $B$ such that for every $n\ge1$ and every $\varepsilon\in(0,1)$ there is an algorithm solving the same problem on every graph with at most $n$ nodes in
--
--   $$A\,T(n)\,\bigl(\log\log(n/\varepsilon+16)\bigr)^{B}$$
--
--   rounds with error probability at most $\varepsilon$. The new algorithm may depend on $n$ and $\varepsilon$.
--
--   With $\varepsilon=2^{-\log^{\gamma}n}$ this solves such problems with error $2^{-\log^\gamma n}$ in $T(n)\,\mathrm{poly}(\log\log n)$ rounds; the dependence of the error on the round count is only through $\log\log(1/\varepsilon)$.
--
--   Differences from the source:
--   - reading: a problem solvable with error n^(−1000) in T(n) rounds and checkable in T(n) rounds → one correctness condition independent of n; for every N, an algorithm with error at most N^(−1000) and a checker deciding the condition, both in T(N) rounds, on graphs with at most N nodes; reason: if the problem may vary with n, the printed theorem is false at n = 1 (take the n = 1 problem unsolvable on one-node graphs: the hypothesis n^(−1000) = 1 is no guarantee, while the conclusion asks error ε < 1)
--   - reading: error probability → probability that the output is not correct (some node rejects); reason: the error of an algorithm solving a problem is the probability its output is not a solution
--   - generalization: a problem → an arbitrary correctness condition on (graph, identifiers, inputs, outputs); reason: every problem of the source is such a condition
--   - encoding: ε(n) a function with values in (0, 1) → for each fixed n, every ε ∈ (0, 1), with A and B uniform; reason: applying the fixed-n statement at each n gives the function form
--   - reading: T(n) · poly(log log(n/ε)) rounds → A · T(n) · (log log(n/ε + 16))^B rounds with absolute A > 0 and B; reason: one polynomial uniform in n, ε, T and the problem; the +16 padding keeps the expression defined and positive for small n/ε
--   - encoding: n the number of nodes → n ≥ 1 an upper bound with card V ≤ n, known to the algorithm; reason: the source allows n to be a global upper bound (p. 2)
--   - encoding: error probability bounds → outer measure of the failure set under the product fair-coin law; reason: published convention of the base mission; no measurability of arbitrary local computation is assumed
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Theorem 4.2, p. 11 (PDF 12); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Supplement_Corollaries

open MeasureTheory

noncomputable section

namespace LocalLLL.Main.Supplement

open LocalLLL.Main

/-- Theorem 4.2, printed p. 11 (PDF 12). The problem is one correctness predicate `Correct`,
independent of the size bound; `chk N` decides it in `T N` rounds on graphs with at most `N`
nodes, and `alg N` solves it in `T N` rounds with failure at most `N^(-1000)` there, for every `N`.
The constants `A`, `B` are absolute. -/
theorem theorem_4_2 :
    ∃ B : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ (I O : Type) (Correct : ∀ V : Type, SimpleGraph V → (V → ℕ) → (V → I) → (V → O) → Prop)
        (T : ℕ → ℕ) (alg : ℕ → LocalAlg I O) (chk : ℕ → LocalAlg (I × O) Bool),
        (∀ (N : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ) (input : V → I)
            (out : V → O), Function.Injective id → Fintype.card V ≤ N →
            (allCorrect (chk N) (T N) G id input out ↔ Correct V G id input out)) →
        (∀ N : ℕ, 1 ≤ N → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
            (input : V → I), Function.Injective id → Fintype.card V ≤ N →
            tapes V {ω | ¬ Correct V G id input (run (alg N) (T N) G id input ω)}
              ≤ ENNReal.ofReal ((N : ℝ) ^ (-1000 : ℝ))) →
        ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ T' : ℕ, (T' : ℝ) ≤ A * (T n : ℝ) * loglogRatio n ε ^ B ∧
        ∃ alg' : LocalAlg I O,
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ) (input : V → I),
            Function.Injective id → Fintype.card V ≤ n →
            tapes V {ω | ¬ Correct V G id input (run alg' T' G id input ω)}
              ≤ ENNReal.ofReal ε := by sorry

end LocalLLL.Main.Supplement
