-- Prove2me | Theorems.Thm_MCPoise_Supplement_theorem_1_4
-- name    : MCPoise.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:16:28.359035+00:00
-- url     : https://prove2.me/theorems/c4732cc9-3b47-457f-a173-288550b0f9d3
-- title:
--   Theorem 1.4 — a polynomial-time $O(\log^9 k)$-approximation for Average Multicommodity Multicast
-- statement:
--   Let $G$ be a graph on $n$ vertices with $k$ demand pairs $(s_i, t_i)$, each connected in $G$. For a telephone-model schedule $S$ on $G$ that delivers every demand, let $C_i(S)$ be the first round at which $t_i$ holds the message of $s_i$.
--
--   **Theorem 1.4.** There are a polynomial-time algorithm and an absolute constant $C$ such that the algorithm outputs a schedule $S$ on $G$ (each round a matching of $G$) delivering every demand, with
--   $$\sum_{i=1}^k C_i(S) \le C \log^9(k+1) \sum_{i=1}^k C_i(S')$$
--   for every schedule $S'$ on $G$ that delivers every demand.
--
--   It is the first polylogarithmic approximation for the sum (equivalently the average) of completion times in multicommodity multicast, and the static ingredient of Theorem 4.2.
--
--   **Formalization Note** The machine and the constant are fixed before the instance. Completion times are counted by demand index; a demand with $s_i = t_i$ completes at time $0$.
--
--   Differences from the source:
--   - reading: constructed in polynomial time / a polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, input `encIn` (n in unary), output `encSched`, polynomial on every input; reason: the source names no machine; the base goal uses the same model
--   - reading: the printed O(·) in log k → the factor log(k+1) with one absolute constant C; reason: log k vanishes at k = 1, where the literal bound is false (one demand s ≠ t on an edge); for k ≥ 2 the two differ by a constant factor
--   - encoding: OPT_avg, the optimal total completion time → comparison with every schedule S′ on G that delivers every demand; reason: the same claim, with no infimum over a possibly empty set
--   - encoding: instances where the problem has a solution → hypothesis that every demand is connected in G; reason: otherwise no schedule delivers and the objective is infinite; the base goal carries the same hypothesis
--   - encoding: a schedule in the telephone model → a list of rounds, each a duplicate-free list of calls on edges that pairwise share no vertex; delivery by time-respecting paths; reason: the same schedules; every matching is the call set of a duplicate-free list
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.4, p.3 (objective p.3; proof in §3, pp.20–24)

import Mathlib
import Definitions.Def_MCPoise_Connects
import Definitions.Def_MCPoise_encIn
import Definitions.Def_MCPoise_Supplement_IsSchedOn
import Definitions.Def_MCPoise_Supplement_Delivers
import Definitions.Def_MCPoise_Supplement_encSched

namespace MCPoise.Supplement

/-- **Theorem 1.4 (polylogarithmic approximation for Average Multicommodity Multicast).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.4, p.3: "There is a polynomial-time O(log⁹ k)-approximation for Average Multicommodity Multicast." The
objective (p.3): "minimize the average, or equivalently the sum, of the times at which each sink `t_i` first receives
the message from its source `s_i`". Proof in §3, pp.20–24.

There are one Turing machine, polynomial in the length of the input on every input, and one absolute constant `C` such
that for every instance whose demands are connected in `G`: the output is a schedule on `G` (every round a matching
of `G`) delivering every demand, and its total completion time `Σ_i complTime_i` is at most
`C · log⁹(k + 1)` times the total completion time of every schedule on `G` that delivers every demand.

**Formalization Note.** OPT_avg is written as "every delivering schedule `S′`", so no infimum has a junk value.
`log(k + 1)` replaces `log k`, which vanishes at `k = 1` where the literal bound is false (one demand `s ≠ t` on an
edge: OPT = 1, bound 0); for `k ≥ 2` the two differ by a constant factor. Without connectivity no schedule delivers, so
it is a hypothesis. Completion times are counted by demand index; a demand with `s_i = t_i` completes at time `0`.
Machine model as in the base goal: `Turing.TM2ComputableInPolyTime` over `Fin 4`, input `encIn`, output `encSched`. -/
theorem theorem_1_4 :
    ∃ alg : Inst → List (List (ℕ × ℕ)), Nonempty (Turing.TM2ComputableInPolyTime encIn encSched alg) ∧
      ∃ C : ℝ, ∀ I : Inst, Connects I I.graph →
        IsSchedOn I.graph (alg I) ∧ Delivers I (alg I) ∧
        ∀ S' : List (List (ℕ × ℕ)), IsSchedOn I.graph S' → Delivers I S' →
          (∑ i : Fin I.k, (complTime I (alg I) i : ℝ)) ≤
            C * Real.log ((I.k : ℝ) + 1) ^ 9 * ∑ i : Fin I.k, (complTime I S' i : ℝ) := by sorry

end MCPoise.Supplement
