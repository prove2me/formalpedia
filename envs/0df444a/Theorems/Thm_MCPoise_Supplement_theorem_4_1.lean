-- Prove2me | Theorems.Thm_MCPoise_Supplement_theorem_4_1
-- name    : MCPoise.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:17:05.108602+00:00
-- url     : https://prove2.me/theorems/3dc22787-7ef8-481b-85b2-dc654fe67027
-- title:
--   Theorem 4.1 — a polynomial-time $O(\log^8 k)$-approximation for MCMVC
-- statement:
--   Let $G$ be a graph with $k$ demand pairs $(s_i, t_i)$, each connected in $G$. For an infinite telephone-model schedule $M$ on $G$, let $l^\tau_v(u) = \tau - \varphi^\tau_v(u)$ be the latency of $v$ with respect to $u$ at time $\tau$. The MCMVC objective of $M$ is $\max_{i}\sup_{\tau \ge 0} l^\tau_{t_i}(s_i)$.
--
--   **Theorem 4.1.** There are a polynomial-time algorithm and an absolute constant $C$ such that the algorithm outputs a nonempty list $P$ of matchings of $G$, and the schedule $M_P$ that repeats $P$ forever satisfies: for every infinite schedule $M'$ on $G$ and every $B$ with $l^\tau_{t_i}(s_i) \le B$ under $M'$ for all $i$ and all $\tau \ge 0$,
--   $$l^\tau_{t_i}(s_i) \le C \log^8(k+1)\, B \quad \text{under } M_P, \text{ for all } i \text{ and } \tau \ge 0.$$
--
--   This is the first polylogarithmic approximation for the multicommodity maximum vector-clock problem.
--
--   **Formalization Note** The objective may be infinite, so the optimum is compared through every bound $B$ on every competing schedule, not through an infimum.
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
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 4.1, p.26 (MCMVC defined in §4.1.1, p.25)

import Mathlib
import Definitions.Def_MCPoise_Connects
import Definitions.Def_MCPoise_encIn
import Definitions.Def_MCPoise_Supplement_IsSchedOn
import Definitions.Def_MCPoise_Supplement_latency
import Definitions.Def_MCPoise_Supplement_periodic
import Definitions.Def_MCPoise_Supplement_encSched

namespace MCPoise.Supplement

/-- **Theorem 4.1 (polylogarithmic approximation for MCMVC).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 4.1, p.26: "There is a polynomial-time O(log⁸ k)-approximation for MCMVC." MCMVC (§4.1.1, p.25): "Given a
graph G and source-sink pairs D, find a schedule M that minimizes `max_{(s,t)∈D} max_{τ≥0} l^τ_t(s)`."

There are one Turing machine, polynomial in the length of the input on every input, and one absolute constant `C` such
that for every instance whose demands are connected in `G`: the output is a nonempty list `P` of matchings of `G`,
and for every infinite schedule `M′` on `G` and every bound `B` with `l^τ_{t_i}(s_i) ≤ B` under `M′` for all demands
`i` and all times `τ`, the schedule that repeats `P` forever has `l^τ_{t_i}(s_i) ≤ C · log⁸(k + 1) · B` for all `i`
and `τ`.

**Formalization Note.** A machine cannot output an infinite sequence; the output is a period, repeated forever (p.4:
"often represented as a periodic sequence"). The comparator `M′` is any infinite schedule, periodic or not. The
objective may be infinite, so OPT is written through bounds `B`, never as an infimum or supremum with a junk value.
`log(k + 1)` replaces `log k`, which vanishes at `k = 1`; for `k ≥ 2` they differ by a constant factor. Machine
model as in the base goal, output `encSched`. -/
theorem theorem_4_1 :
    ∃ alg : Inst → List (List (ℕ × ℕ)), Nonempty (Turing.TM2ComputableInPolyTime encIn encSched alg) ∧
      ∃ C : ℝ, ∀ I : Inst, Connects I I.graph →
        alg I ≠ [] ∧ IsSchedOn I.graph (alg I) ∧
        ∀ M' : ℕ → List (ℕ × ℕ), IsInfSchedOn I.graph M' → ∀ B : ℝ,
          (∀ (i : Fin I.k) (τ : ℕ), (latency M' (I.t i).val (I.s i).val τ : ℝ) ≤ B) →
          ∀ (i : Fin I.k) (τ : ℕ), (latency (periodic (alg I)) (I.t i).val (I.s i).val τ : ℝ) ≤
            C * Real.log ((I.k : ℝ) + 1) ^ 8 * B := by sorry

end MCPoise.Supplement
