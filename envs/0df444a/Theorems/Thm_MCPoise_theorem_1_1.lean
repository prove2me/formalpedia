-- Prove2me | Theorems.Thm_MCPoise_theorem_1_1
-- name    : MCPoise.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:59.22398+00:00
-- url     : https://prove2.me/theorems/28c13752-e893-4117-b86b-c7c1b65656b0
-- title:
--   Theorem 1.1 — an efficient $O(\log^6 k)$-approximation for MC Poise
-- statement:
--   Let $G = (V, E)$ be an undirected graph with $k$ demand pairs $(s_i, t_i)$, each connected in $G$. Write $\mathrm{poise}_D(H) = \max_{v} \deg_H(v) + \max_{i} \mathrm{dist}_H(s_i, t_i)$ for a subgraph $H$ connecting every pair.
--
--   **Theorem 1.1.** There are a polynomial-time algorithm and an absolute constant $C$ such that the output $H$ is a subgraph of $G$ connecting every demand and
--   $$\mathrm{poise}_D(H) \le C \log^6(k+1) \cdot \mathrm{poise}_D(H')$$
--   for every subgraph $H'$ of $G$ connecting every demand.
--
--   This is the paper's main result, and with Theorem 1.2 of the paper it gives the first polylogarithmic approximation for multicommodity multicast on general undirected graphs.
--
--   **Formalization Note** The machine and the constant are fixed before the instance. Every instance is covered: all $n$ and $k$, repeated demands, $s_i = t_i$ and optimal value $0$.
--
--   Differences from the source:
--   - reading: an efficient, polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, polynomial in a fixed binary encoding on every input; reason: the source names no machine, and every step it describes is deterministic
--   - encoding: an undirected graph with demand pairs, of unstated input size → vertices Fin n; n in unary, then the edge and demand lists in binary; reason: this is the usual graph size, and the paper's running times are in n (p.21)
--   - reading: the printed $O(\cdot)$ in $\log k$ → the factor $\log(k+1)$ with one absolute constant; reason: $\log k$ vanishes at $k = 1$, and for $k \ge 2$ the two differ by a constant factor
--   - encoding: minimum poise subgraph, OPT → comparison with every connecting subgraph H′ ≤ G; reason: the same claim, with no infimum over a possibly empty set
--   - encoding: instances where the problem has a solution → hypothesis that every demand is connected in G; reason: Definition 1 requires H to connect every pair, so otherwise no feasible H exists
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.1, p.3

import Mathlib
import Definitions.Def_MCPoise_Connects
import Definitions.Def_MCPoise_poise
import Definitions.Def_LCPlanarSteiner_sgOf
import Definitions.Def_MCPoise_encIn

namespace MCPoise

/-- **Theorem 1.1 (polylogarithmic approximation for MC Poise).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Theorem 1.1, p.3: "There is an efficient algorithm that yields an O(log⁶ k)-approximation for MC Poise."

There are one Turing machine, polynomial in the length of the input on every input, and one absolute constant `C` such that for every instance whose demands are connected in `G`: the output `H` is a subgraph
of `G` connecting every demand, and `poise_D(H) ≤ C · log⁶(k + 1) · poise_D(H′)` for every subgraph `H′` of `G` connecting every demand.

**Formalization Note.** The machine and the constant are fixed before the instance. Machine model: Mathlib's deterministic `Turing.TM2ComputableInPolyTime` over `Fin 4`, with `n` in unary (the source names none). OPT is written as "every
connecting `H′`", so no infimum has a junk value, and `Connects` is a separate clause on both `H` and `H′` since `SimpleGraph.dist` is `0` on an unreachable pair. `log(k + 1)` replaces `log k`, which vanishes at `k = 1`, where the literal
reading is false (one edge, one demand: poise `2`, bound `0`); for `k ≥ 2` the two differ by a constant. At `k = 0`, or when `s_i = t_i` for all `i`, the bound forces `H` to have no edge. -/
theorem theorem_1_1 :
    ∃ alg : Inst → List (ℕ × ℕ), Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∃ C : ℝ, ∀ I : Inst, Connects I I.graph →
        LCPlanarSteiner.sgOf I.n (alg I) ≤ I.graph ∧
        Connects I (LCPlanarSteiner.sgOf I.n (alg I)) ∧
        ∀ H' : SimpleGraph (Fin I.n), H' ≤ I.graph → Connects I H' →
          (poise I (LCPlanarSteiner.sgOf I.n (alg I)) : ℝ) ≤
            C * Real.log ((I.k : ℝ) + 1) ^ 6 * (poise I H' : ℝ) := by sorry

end MCPoise
