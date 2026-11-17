-- Prove2me | Theorems.Thm_MCPoise_Supplement_theorem_4_2
-- name    : MCPoise.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:17:44.23397+00:00
-- url     : https://prove2.me/theorems/dbe28872-0629-4592-bc93-e329e6ffe9cb
-- title:
--   Theorem 4.2 — a polynomial-time $O(\log^9 k\log n)$-approximation for MCAVC
-- statement:
--   Let $G$ be a graph on $n$ vertices with $k$ demand pairs $(s_i, t_i)$, each connected in $G$. For an infinite telephone-model schedule $M$ on $G$, let $l^\tau_v(u) = \tau - \varphi^\tau_v(u)$ be the latency. The MCAVC objective of $M$ is $\sup_{\tau \ge 0} \sum_{i=1}^k l^\tau_{t_i}(s_i)$.
--
--   **Theorem 4.2.** There are a polynomial-time algorithm and an absolute constant $C$ such that the algorithm outputs a nonempty list $P$ of matchings of $G$, and the schedule $M_P$ that repeats $P$ forever satisfies: for every infinite schedule $M'$ on $G$ and every $B$ with $\sum_i l^\tau_{t_i}(s_i) \le B$ under $M'$ for all $\tau \ge 0$,
--   $$\sum_{i=1}^k l^\tau_{t_i}(s_i) \le C \log^9(k+1)\log n \cdot B \quad \text{under } M_P, \text{ for all } \tau \ge 0.$$
--
--   This is the first polylogarithmic approximation for the multicommodity average vector-clock problem.
--
--   **Formalization Note** The sum is over demand indices. $\log n$ is literal: it is positive whenever some $s_i \ne t_i$, and when every $s_i = t_i$ both objectives are $0$.
--
--   Differences from the source:
--   - reading: constructed in polynomial time / a polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, input `encIn` (n in unary), output `encSched`, polynomial on every input; reason: the source names no machine; the base goal uses the same model
--   - reading: the solution is an infinite sequence of matchings, output in polynomial time → the machine outputs a finite nonempty list of matchings of G, repeated forever; the comparator is any infinite schedule; reason: a machine cannot output an infinite sequence; p.4: "often represented as a periodic sequence"
--   - reading: the printed O(·) in log k → the factor log(k+1) with one absolute constant C; reason: log k vanishes at k = 1, where the literal bound is false (one demand s ≠ t on an edge); for k ≥ 2 the two differ by a constant factor
--   - encoding: OPT, the minimum of a possibly infinite objective → every infinite schedule M′ on G and every bound B on its objective; reason: the same claim, with no infimum or supremum taking a junk value
--   - reading: ϕ^t_v(u), the latest time whose information of u can arrive at v by time t → round τ is M τ (τ ≥ 1); information of time t′ travels in rounds t′+1, …, τ; ϕ is 0 when no such t′ exists; reason: the source leaves the round indexing implicit; ϕ ≥ 0 is its convention ϕ⁰ = 0; the same definition serves output and comparator
--   - encoding: instances where the problem has a solution → hypothesis that every demand is connected in G; reason: otherwise no schedule delivers and the objective is infinite; the base goal carries the same hypothesis
--   - encoding: a schedule in the telephone model → a list of rounds, each a duplicate-free list of calls on edges that pairwise share no vertex; delivery by time-respecting paths; reason: the same schedules; every matching is the call set of a duplicate-free list
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 4.2, p.26 (MCAVC defined in §4.1.1, p.25)

import Mathlib
import Definitions.Def_MCPoise_Connects
import Definitions.Def_MCPoise_encIn
import Definitions.Def_MCPoise_Supplement_IsSchedOn
import Definitions.Def_MCPoise_Supplement_latency
import Definitions.Def_MCPoise_Supplement_periodic
import Definitions.Def_MCPoise_Supplement_encSched

namespace MCPoise.Supplement

/-- **Theorem 4.2 (polylogarithmic approximation for MCAVC).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 4.2, p.26: "There is a polynomial-time O(log⁹ k log n)-approximation for MCAVC." MCAVC (§4.1.1, p.25):
"Given a graph G and source-sink pairs D, find a schedule M that minimizes `max_{τ≥0} Σ_{(s,t)∈D} l^τ_t(s)`."

There are one Turing machine, polynomial in the length of the input on every input, and one absolute constant `C` such
that for every instance whose demands are connected in `G`: the output is a nonempty list `P` of matchings of `G`,
and for every infinite schedule `M′` on `G` and every bound `B` with `Σ_i l^τ_{t_i}(s_i) ≤ B` under `M′` for all
times `τ`, the schedule that repeats `P` forever has `Σ_i l^τ_{t_i}(s_i) ≤ C · log⁹(k + 1) · log n · B` for all `τ`.

**Formalization Note.** The output is a period, repeated forever (p.4); the comparator `M′` is any infinite schedule.
The objective may be infinite, so OPT is written through bounds `B`. The sum is over demand indices. `log(k + 1)`
replaces `log k`, which vanishes at `k = 1`; `log n` is literal: it is positive whenever some `s_i ≠ t_i` (then
`n ≥ 2`), and if every `s_i = t_i` both objectives are `0`. Machine model as in the base goal, output `encSched`. -/
theorem theorem_4_2 :
    ∃ alg : Inst → List (List (ℕ × ℕ)), Nonempty (Turing.TM2ComputableInPolyTime encIn encSched alg) ∧
      ∃ C : ℝ, ∀ I : Inst, Connects I I.graph →
        alg I ≠ [] ∧ IsSchedOn I.graph (alg I) ∧
        ∀ M' : ℕ → List (ℕ × ℕ), IsInfSchedOn I.graph M' → ∀ B : ℝ,
          (∀ τ : ℕ, (∑ i : Fin I.k, (latency M' (I.t i).val (I.s i).val τ : ℝ)) ≤ B) →
          ∀ τ : ℕ, (∑ i : Fin I.k, (latency (periodic (alg I)) (I.t i).val (I.s i).val τ : ℝ)) ≤
            C * Real.log ((I.k : ℝ) + 1) ^ 9 * Real.log (I.n : ℝ) * B := by sorry

end MCPoise.Supplement
