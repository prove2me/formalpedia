-- Prove2me | Theorems.Thm_NetBilinear_Supplement_theorem_3
-- name    : NetBilinear.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:44:36.497838+00:00
-- url     : https://prove2.me/theorems/073c435b-b992-57bd-98b0-995cb304bb74
-- title:
--   Theorem 3 (corrected: Prop. 6 (iii) over $\tilde{\mathcal I}\cup\tilde{\mathcal I}^j$) — Algorithm 1 on a forest structure gives an EC&R assignment of class $l^\pm$
-- statement:
--   Let $G=(V,A)$ be a finite network without self-loops (parallel arcs allowed), whose network polytope $\Xi$ is described by the flow-balance rows $i^+,i^-$ of its augmented node-arc incidence matrix and the arc bounds. Let $y\in\Delta_m$ with $m=|M|>1$, and let the class $l$ have base equality $y_{j'}x_{i'}-z_l=0$ (with $i'\in A$ and $j'\in M$).
--
--   For each $j\in M$, let $\bar F^j$ be a forest of the parallel network $G^j$, composed of trees $\bar T^j_k$ ($k\in\Gamma_j$), with node set $\tilde{\mathcal I}^j$. Let $\tilde{\mathcal I}\subseteq V$ be the connection nodes and $\tilde{\mathcal J}\subseteq A$ the connection arcs. Assume these data satisfy conditions (i)–(iii) of Propositions 4 and 6, with Proposition 6 (iii) read over $\tilde{\mathcal I}\cup\tilde{\mathcal I}^j$ (see below). Then for both signs $\sigma\in\{+,-\}$ and every final state of every terminating run of Algorithm 1:
--   1. every member of $\tilde{\mathcal I}^j$ ($j\in M$), $\tilde{\mathcal I}$ and $\tilde{\mathcal J}$ has received a label, and
--   2. the output
--   $$
--   [\mathcal I_1,\dots,\mathcal I_m,\bar{\mathcal I}\,|\,\mathcal J,\bar{\mathcal J}]
--   $$
--   is an EC&R assignment of class $l^\sigma$ for the network rows.
--
--   This is the converse of Propositions 4 and 6. It identifies EC&R assignments, and with them EC&R inequalities for $\operatorname{conv}(\mathcal S)$, from forest structures in the parallel networks, without searching for aggregation weights.
--
--   **Formalization Note** The EC&R assignment is `IsECRAssignment` for the rows `G.incRow`, with bilinear terms $y_jx_k$, $j\in M$, $k\in A$. Its weights are existential: the unit weights of the paper's proof are not part of the statement.
--
--   Differences from the source:
--   - correction: Proposition 6 (iii), "each node in Ĩ ∩ Ĩj … is adjacent to no other nodes in that set" (that set = Ĩ ∩ Ĩj) → adjacent to no node of Ĩ ∪ Ĩj; reason: as printed the theorem is false. Take m = 2, V = {p, u, w}, arcs i′ = (p, w) and a = (u, w), j′ = 1, Ĩ1 = {u, w}, Ĩ2 = ∅, Ĩ = {u}, J̃ = ∅. Every printed condition holds, and Algorithm 1 (class l+) outputs I1 = {w+, u+}, I2 = ∅, Ī = {u−}. That needs 3 canceled terms, but only y1x_{i′} and y1x_a can cancel (y2x_a is created by u− alone). The proof of Prop. 6 (iii), p.18, rules out every other flow-balance constraint creating the term, i.e. every node of Ĩ ∪ Ĩj.
--   - generalization: the assignment obtained from Algorithm 1 is an EC&R assignment → in addition, every member of Ĩj, Ĩ and J̃ is labelled at termination; reason: this is step (I) of the paper's proof, p.18, and makes the output of lines 47–59 well defined; dropping the conjunct gives the source's claim.
--   - reading: a network G = (V, A) with node-arc incidence matrix → the published NetBilinear.Network, which excludes self-loops; reason: a node-arc incidence matrix has no self-loop column, as in the published base mission.
--   - encoding: the assignment "obtained from Algorithm 1" → the output of every final state of every terminating run, with line 9's choice of i ∈ D free; reason: the algorithm is nondeterministic, and the theorem holds for each of its runs.
--   - encoding: class l with A^l_{j′i′} = 1 → the pair (i′, j′); reason: the EC&R conditions depend on l only through its base term y_{j′}x_{i′}.
--   - encoding: forests F̄j with trees T̄jk, k ∈ Γj, an index set → finite families of node-disjoint trees of Ḡ covering Ĩj; reason: a forest is the disjoint union of its trees, and disjoint nonempty node sets in a finite V are finitely many.
--   - encoding: Ḡ, adjacency in the parallel networks, Definition 2 → Ḡ as a SimpleGraph, replicas named as in G (p.12), and Definition 2 on node sets only; reason: parallel arcs give the same adjacency, and Definition 2 uses only node sets, adjacency and incidence.
--   - reading: the label l(i) of a node i that lies in several of Ĩ1, …, Ĩm and Ĩ → one member, with its own label, per set containing it (the replica (i, j) for each Ĩj, and i as a connection node), each processed by the block of lines 10–21 or 22–36 of its kind; reason: line 23 labels the copy "k ∈ Ĩj such that k = i" of a connection node i separately, and lines 47–52 read the label once per set.
--   - reading: lines 38 and 41, "for each unlabeled node k = t(i) ∈ Ĩj and k̄ = h(i) ∈ Ĩj" → each endpoint of the arc i is labelled on its own whenever it is unlabeled and in the set; reason: one endpoint may be absent from the set or already labelled, and Example 5, p.21, applies lines 38–40 to node 8 alone.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, Theorem 3, p.18 (proof pp.18–19); Algorithm 1, p.20; Propositions 4 and 6, pp.12 and 17; Definition 2, p.12

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_Supplement_IsECRAssignment
import Definitions.Def_NetBilinear_Supplement_VerticallyConnected
import Definitions.Def_NetBilinear_Supplement_ForestConditions
import Definitions.Def_NetBilinear_Supplement_Algorithm1

namespace NetBilinear.Supplement

/-- **Theorem 3: the assignment produced by Algorithm 1 from a forest structure satisfying the
conditions of Propositions 4 and 6 is an EC&R assignment of class `l±`.**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, Theorem 3, p.18: "Consider set S with Ξ that represents the network polytope
corresponding to the network G = (V,A). Let F̄j, for each j ∈ M, be a forest in the parallel
network Gj, composed of trees T̄jk for k ∈ Γj, where Γj is an index set, that satisfies the
conditions (i)–(iii) of Propositions 4 and 6 with the corresponding node sets Ĩj, the connection
node set Ĩ, the connection arc set J̃, and the class l. Then, the assignment
[I1,...,Im, Ī | J, J̄] obtained from Algorithm 1 is an EC&R assignment for class-l±."

Hypotheses: `G` is a finite network without self-loops (parallel arcs allowed), `m = |M| > 1`
(§3.2, p.10), the class `l` has its unique entry `A^l_{j'i'} = 1` (base term `y_{j'} x_{i'}`),
and the trees `T j k` (`k ∈ Γ j`) of the forests `F̄^j`, with node sets `Ĩ_j = It j`,
connection nodes `Ĩ = Ic` and connection arcs `J̃ = Jc`, satisfy conditions (i)–(iii) of
Propositions 4 and 6 (`ForestConditions`). For both class signs `σ` ("class-l±") and every
final state `st` of every terminating run of Algorithm 1:
1. every member of `Ĩ_j` (each `j`), `Ĩ` and `J̃` has received a label, and
2. the output `[I_1, …, I_m, Ī | J, J̄]` of lines 47–59 is an EC&R assignment of class `l^σ`
   for the network rows `E = G.incRow` (bilinear terms `y_j x_k`, `j ∈ M`, `k ∈ A`).

**Formalization Note.** (Correction.) `ForestConditions` states Proposition 6 (iii) with
"adjacent to no other node of `Ĩ ∪ Ĩ_j`" in place of the printed "adjacent to no other nodes
in that set" (`Ĩ ∩ Ĩ_j`), under which the theorem is false: for `m = 2`, `V = {p, u, w}`, arcs
`i' = (p, w)`, `a = (u, w)`, `j' = 1`, `Ĩ_1 = {u, w}`, `Ĩ_2 = ∅`, `Ĩ = {u}`, `J̃ = ∅`, every
printed condition holds, Algorithm 1 outputs `I_1 = {w⁺, u⁺}`, `Ī = {u⁻}` (class `l⁺`), which
needs 3 canceled terms while only `y_1x_{i'}` and `y_1x_a` can cancel. Conclusion 1 is step (I)
of the proof (p.18–19); it makes the output of lines 47–59 well defined. -/
theorem theorem_3 {V A M : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    [Fintype M] [DecidableEq M] (hm : 1 < Fintype.card M)
    (G : Network V A) (i' : A) (j' : M) (It : M → Finset V) (Ic : Finset V) (Jc : Finset A)
    (Γ : M → Type*) [∀ j, Fintype (Γ j)] (T : (j : M) → Γ j → G.underlying.Subgraph)
    (hF : ForestConditions G It Ic Jc i' j' Γ T)
    (σ : Sign) (st : State V A M) (hrun : Algorithm1 G It Ic Jc i' j' σ st) :
    (∀ k, IsMember It Ic Jc k → st.lab k ≠ none) ∧
    IsECRAssignment G.incRow i' j' σ (alg1I It st) (alg1Ibar Ic st) (alg1J Jc st)
      (alg1Jbar Jc st) := by sorry

end NetBilinear.Supplement
