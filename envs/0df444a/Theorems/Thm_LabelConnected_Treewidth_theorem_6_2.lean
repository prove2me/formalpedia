-- Prove2me | Theorems.Thm_LabelConnected_Treewidth_theorem_6_2
-- name    : LabelConnected.Treewidth.theorem_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:28:54.142815+00:00
-- url     : https://prove2.me/theorems/fe09e44e-965f-4f05-a1b7-70ab0ce89fb3
-- title:
--   Theorem 6.2 — Gossiping is decided, and a temporally connecting labeling constructed, deterministically in 2^{O(tw)}·n time
-- statement:
--   Gossiping can be solved deterministically in $2^{O(\mathrm{tw})} \cdot n$ time, where $\mathrm{tw}$ is the treewidth of the support of the input multigraph; if the input is a yes-instance, a temporally connecting labeling can be computed within the same time.
--
--   In the Lean statement: there are one deterministic program $P$ of the integer RAM (unit cost, no coins, no oracle) and constants $C, W \in \mathbb N$, fixed before the input, such that for every multigraph $G$ on vertices $0, \dots, n-1$ with $m$ edges (loops and parallel edges allowed), given as $[n, m, u_1, v_1, \dots, u_m, v_m]$, every register at every step has at most $W(1 + \log_2(2 + n + m))$ bits, and $P$ halts within
--   $$C\,(n + m) + C \cdot 2^{C \cdot \mathrm{tw}} \cdot (n + 1)$$
--   steps, $\mathrm{tw}$ the treewidth of the support of $G$, with output $[1, \lambda(e_1), \dots, \lambda(e_m)]$ for a temporal labeling $\lambda$ under which $(G, \lambda)$ is temporally connected when $G$ is a yes-instance, and $[0]$ when it is not. No tree decomposition is given to the program.
--
--   The bound is single-exponential in treewidth and linear in $n$; by Corollary 8.10 of the paper, no $2^{o(\mathrm{tw})} n^{O(1)}$ algorithm exists under ETH. The theorem is the hub of the paper's parameterized landscape.
--
--   Differences from the source:
--
--   - encoding: an undirected multigraph G = (V, E), parallel edges distinct, loops allowed → vertices Fin n, a finite edge type E and an endpoint map ends : E → Fin n × Fin n (a loop is an edge with equal endpoints, parallel edges are distinct edges with the same unordered endpoint pair); reason: Lean convention; every finite multigraph is one of these up to renaming
--   - encoding: λ: E → N assigning one positive integer to each edge → lab : E → ℕ with 0 < lab e for every edge e; reason: ℕ contains 0 in Lean
--   - encoding: a strict temporal path traversing edges e1, …, eℓ with λ(e1) < ··· < λ(eℓ), paths without repeated vertices, length 0 allowed → ℓ ∈ ℕ, an injective vertex sequence v : Fin (ℓ+1) → Fin n from u to w, edges e i joining v i and v (i+1), labels strictly increasing; reason: the paper's path convention (p. 6) written out
--   - generalization: 2^{O(tw)}·n time under the convention that the input has been cleaned up (p. 19: "for an arbitrary input, add O(n + m) time to read and clean up its edge list") → one constant C with at most C·(n + m) + C·2^{C·tw}·(n + 1) steps on every multigraph input; reason: the paper's own convention for arbitrary inputs; on clean inputs m ≤ 3·tw·n, so n + m ≤ (3·tw + 1)·n and the bound is 2^{O(tw)}·n as printed
--   - encoding: the word RAM with Θ(log(n+m))-bit words; deterministic → one program of the published integer RAM CongruencyTU without coin or query instructions (MinDegST.AddOne.Deterministic), registers within W·(1 + ⌊log₂(2 + n + m)⌋) bits at every step (WordBounded), halting within the bound (HaltsWithin); reason: O(·) as explicit universal constants on one fixed machine; the word bound keeps unit-cost arithmetic honest
--   - encoding: tw, the treewidth of the support (−1 for the empty graph) → PlantedSubgraphLD.tw (support (ofList es)), which is 0 for the empty graph, and the factor n + 1 in place of n; reason: the empty and one-vertex inputs are absorbed by the constant
--   - encoding: Gossiping solved; a temporally connecting labeling computed within the same time on yes-instances → a single run whose output is [1, λ(e1), …, λ(em)] with λ positive and temporally connecting on yes-instances, and [0] on no-instances; reason: a fixed output format for the decision and the labeling; the proof produces both in one run
--   - encoding: the input multigraph (and edge sets / witnesses handed to the algorithm) → [n, m, u1, v1, …, um, vm] (MinDegST.AddOne.encGraph), edge e_i referred to by its index i − 1, an edge set as its length followed by its indices, each once, in any order; reason: a running time needs a fixed input representation; the edge-list representation is the paper's (p. 18, proof of Lemma 5.1)
-- source:
--   Klasing, Mertzios, Molter, Morawietz, Spirakis, Recognizing Label-Connected Graphs, arXiv:2611.05144 (PDF sha256 8dde27a5…), p. 25, Theorem 6.2

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_LabelConnected_Treewidth_Multigraph
import Definitions.Def_LabelConnected_Treewidth_Temporal
import Definitions.Def_LabelConnected_Treewidth_Encoding

open Classical

namespace LabelConnected.Treewidth

/-- **Theorem 6.2.** One deterministic word-RAM program `P` and constants `C, W`, fixed before the
input, such that on every multigraph `G` (vertices `Fin n`, edge list `es` with `m = |es|`, loops and
parallel edges allowed, given as `[n, m, u₁, v₁, …, u_m, v_m]`) every register stays within
`W · (1 + log₂(2 + n + m))` bits, and `P` halts within `C·(n + m) + C·2^{C·tw}·(n + 1)` steps,
`tw` the treewidth of the support of `G`, with output `[1, λ(e₁), …, λ(e_m)]` for a temporally
connecting temporal labeling `λ` if `G` is a yes-instance of Gossiping, and `[0]` if it is not. -/
theorem theorem_6_2 :
    ∃ (P : CongruencyTU.Program) (C W : ℕ), MinDegST.AddOne.Deterministic P ∧
      ∀ (n : ℕ) (es : List (Fin n × Fin n)),
        MinDegST.AddOne.WordBounded P (MinDegST.AddOne.encGraph n es) W (n + es.length) ∧
        MinDegST.AddOne.HaltsWithin P (MinDegST.AddOne.encGraph n es)
          ((C : ℝ) * ((n : ℝ) + (es.length : ℝ)) +
            (C : ℝ) * (2 : ℝ) ^ (C * PlantedSubgraphLD.tw (support (ofList es))) * ((n : ℝ) + 1))
          (IsGossipingOutput es) := by sorry

end LabelConnected.Treewidth
