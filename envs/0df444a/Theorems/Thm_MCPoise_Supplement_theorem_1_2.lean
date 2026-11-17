-- Prove2me | Theorems.Thm_MCPoise_Supplement_theorem_1_2
-- name    : MCPoise.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:15:49.55385+00:00
-- url     : https://prove2.me/theorems/35a0666e-a805-4b8b-9e12-8223e8f0fc2b
-- title:
--   Theorem 1.2 — a multicast schedule of length $O(L\log^2 k)$ from a subgraph of poise $L$
-- statement:
--   Let $H$ be a graph on $n$ vertices with $k \ge 2$ demand pairs $(s_i, t_i)$, each connected in $H$, and let $L = \mathrm{poise}_D(H) = \max_v \deg_H(v) + \max_i \mathrm{dist}_H(s_i, t_i)$.
--
--   **Theorem 1.2.** There are a polynomial-time algorithm and an absolute constant $C$ such that, given $H$ and the demands, the algorithm outputs a telephone-model schedule whose calls are edges of $H$, each round a matching of $H$, that delivers the message of every $s_i$ to $t_i$, and whose length is at most
--   $$C \cdot L \cdot \log^2 k.$$
--
--   Together with the observation that an optimal schedule of length $T$ uses a subgraph of poise at most $2T$, this turns an $\alpha$-approximation for MC Poise into an $O(\alpha\log^2 k)$-approximation for minimum multicommodity multicast time.
--
--   **Formalization Note** The machine and the constant are fixed before the instance. No positivity of $L$ is assumed: if every $s_i = t_i$ and $H$ has no edge, $L = 0$ and the empty schedule is required.
--
--   Differences from the source:
--   - reading: constructed in polynomial time / a polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, input `encIn` (n in unary), output `encSched`, polynomial on every input; reason: the source names no machine; the base goal uses the same model
--   - encoding: given a subgraph of poise L → the input is an instance whose graph is H, with every demand connected in H; L = poise_D(H) is computed from it; reason: poise is defined only for H connecting every demand (Definition 1); Appendix A: "Let H be the given subgraph"
--   - encoding: a schedule of length O(L log² k) → length ≤ C · poise_D(H) · (log k)² with one absolute constant C; reason: an O(·) bound uniform over instances; k ≥ 2 is printed, so log k > 0
--   - encoding: a schedule in the telephone model → a list of rounds, each a duplicate-free list of calls on edges that pairwise share no vertex; delivery by time-respecting paths; reason: the same schedules; every matching is the call set of a duplicate-free list
--   - generalization: a multicommodity multicast schedule (in the communication graph G ⊇ H) → a schedule whose calls are edges of H; the ambient graph G is not part of the input; reason: a schedule on H is a schedule on every G ⊇ H, so the Lean statement implies the source's
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.2, p.3 (proof in Appendix A, p.34)

import Mathlib
import Definitions.Def_MCPoise_Connects
import Definitions.Def_MCPoise_poise
import Definitions.Def_MCPoise_encIn
import Definitions.Def_MCPoise_Supplement_IsSchedOn
import Definitions.Def_MCPoise_Supplement_Delivers
import Definitions.Def_MCPoise_Supplement_encSched

namespace MCPoise.Supplement

/-- **Theorem 1.2 (a short schedule from a low-poise subgraph).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.2, p.3: "Given a subgraph of poise L for k ≥2 demand pairs, a multicommodity multicast schedule of
length O(L log² k) can be constructed in polynomial time." Proof in Appendix A, p.34.

There are one Turing machine, polynomial in the length of the input on every input, and one absolute constant `C` such
that for every instance `I` with `k ≥ 2` demands, whose graph `H = I.graph` (the given subgraph) connects every demand:
the output is a schedule on `H` (every round a matching of `H`) that delivers every demand, of length at most
`C · poise_D(H) · (log k)²`.

**Formalization Note.** The input is the subgraph `H` itself, as an instance whose graph is `H` (Appendix A: "Let `H`
be the given subgraph"); `L = poise_D(H)` is computed from it. `poise` is defined for `H` connecting every demand
(Definition 1), hence the `Connects` hypothesis. `k ≥ 2` is printed, so `log k > 0`. No `0 < L` is assumed: when
every `s_i = t_i` and `H` has no edge, `L = 0` and the empty schedule is required. The machine and `C` are fixed
before the instance; machine model: Mathlib's deterministic `Turing.TM2ComputableInPolyTime` over `Fin 4`, input
`encIn` (`n` in unary), output `encSched`. -/
theorem theorem_1_2 :
    ∃ alg : Inst → List (List (ℕ × ℕ)), Nonempty (Turing.TM2ComputableInPolyTime encIn encSched alg) ∧
      ∃ C : ℝ, ∀ I : Inst, 2 ≤ I.k → Connects I I.graph →
        IsSchedOn I.graph (alg I) ∧ Delivers I (alg I) ∧
        ((alg I).length : ℝ) ≤ C * (poise I I.graph : ℝ) * Real.log (I.k : ℝ) ^ 2 := by sorry

end MCPoise.Supplement
