-- Prove2me | Theorems.Thm_MinDegST_AddOne_theorem_1_1
-- name    : MinDegST.AddOne.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:08.898198+00:00
-- url     : https://prove2.me/theorems/4826f029-c926-46fe-99a1-644b076c5ca7
-- title:
--   Theorem 1.1 — a deterministic algorithm computes a spanning tree of maximum degree ≤ Δ⋆ + 1 in m·n^(1/2+o(1)) time
-- statement:
--   There are one deterministic word-RAM program $P$ and a word-width constant, both fixed before $\varepsilon$, such that for every $\varepsilon>0$ there is $K_\varepsilon>0$ with: on every connected simple graph $G$ with $n$ nodes and $m$ edges, given as an edge list in any order, $P$ halts within
--   $$K_\varepsilon\cdot m\cdot n^{1/2+\varepsilon}+K_\varepsilon$$
--   steps and outputs the edges of a spanning tree $T$ of $G$ with
--   $$\max_{u}\deg_T(u)\ \le\ \Delta^\star(G)+1 .$$
--   The program is given only the graph, not $\Delta^\star(G)$, which is NP-hard to compute. Fürer and Raghavachari (1992) achieved the guarantee $\Delta^\star+1$, the best possible in polynomial time unless P = NP, in $\tilde O(mn)$ time, and [BFW26] in $\tilde O(mn^{3/4})$; this theorem brings the time to $m\,n^{1/2+o(1)}$.
--
--   **Formalization Note.** Part III's subroutines use the value $\Delta^\star$; how the algorithm runs without it is not argued in the paper (insight I2) — the statement is posed as printed, with $\Delta^\star$ not in the input.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm (no machine model fixed) → one program of the CongruencyTU integer RAM (unit cost, no coin or query instruction), with one width constant fixed with the program bounding every register at every step by width·(1 + ⌊log₂(2 + scale)⌋) bits; reason: the paper fixes no machine; logarithmic words keep unit-cost arithmetic from trivializing running times; the external max-flow goal is stated on the same machine
--   - reading: Ô(m√n) time (footnote 1: Ô hides subpolynomial in n factors) → one program fixed first; ∀ ε > 0 ∃ K_ε > 0: cost ≤ K_ε·m·n^{1/2+ε} + K_ε on every input; reason: the standard reading of n^{o(1)} factors with explicit constants; the additive K_ε covers n = 1, m = 0
--   - encoding: given an undirected graph; computes a spanning tree → a connected simple graph on Fin n given as [n, m, u₁, v₁, …] with edges in any order and orientation; output the n − 1 tree edges, each once, as endpoint pairs; reason: the MDST problem is posed on connected graphs (§1); a concrete input/output layout for the RAM
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 1, Theorem 1.1 (restated and proved p. 35)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine

namespace MinDegST.AddOne

/-- **Theorem 1.1.** One deterministic word-RAM program `P` with word-width constant `width`, both
fixed before `ε`, such that for every `ε > 0` there is `K_ε > 0` with: on every connected simple
graph `G` on `Fin n` given as an edge list `es` (`m = |es|`, any order), `P` halts within
`K_ε · m · n^{1/2+ε} + K_ε` steps and outputs the edges of a spanning tree of `G` of maximum degree
at most `Δ⋆(G) + 1`. `Δ⋆(G)` is not part of the input. -/
theorem theorem_1_1 :
    ∃ (P : CongruencyTU.Program) (width : ℕ), Deterministic P ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
        G.Connected → IsEdgeListOf G es →
          WordBounded P (encGraph n es) width (n + es.length)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)),
          G.Connected → IsEdgeListOf G es →
            HaltsWithin P (encGraph n es)
              (K * (es.length : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) + K)
              (fun out => ∃ T : SimpleGraph (Fin n), EncodesEdges out T ∧
                IsSpanningTree G T ∧ ∀ v, deg T v ≤ optDeg G + 1) := by sorry

end MinDegST.AddOne
