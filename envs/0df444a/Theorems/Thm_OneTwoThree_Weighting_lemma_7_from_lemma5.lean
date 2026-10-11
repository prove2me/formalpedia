-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_7_from_lemma5
-- name    : OneTwoThree.Weighting.lemma_7_from_lemma5
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-11T08:59:34.089401+00:00
-- url     : https://prove2.me/theorems/6655c4ee-995d-496f-b728-21006c8f4542
-- title:
--   Lemma 7 from Lemma 5 — elementary parity/coloring transfer for a good R-B-partition
-- statement:
--   The elementary reduction Lemma 5 ⇒ Lemma 7 (Keusch, *A Solution to the 1-2-3
--   Conjecture*, arXiv:2303.02611v4, p. 8). Let $(R,B)$ be a good $R$-$B$-partition of
--   the connected graph $G$: $V = R \cup B$ disjointly, $R$ independent, $G(R,B)$
--   connected, $|B|$ even.
--
--   The paper applies Lemma 5 (`OneTwoThree.Weighting.lemma_5`,
--   `18cd221d-d23a-4ae5-97c8-ca2db074a231`) to the **bipartite subgraph** $G(R,B)$ --
--   not to $G$ -- with $R' := \emptyset$ and $\alpha$ **odd-valued** on $B$
--   ($\alpha(v) \in \{2\deg_{G(R,B)}(v)-1,\,2\deg_{G(R,B)}(v)+1\}$). Then the
--   $\mathsf{hpar}$ hypothesis $\mathrm{Even}(|R'| + \sum_{v\in B}\alpha(v))$
--   reduces to $|B|$ even, which is a good-partition hypothesis. (Note: $R' := R$
--   would put *odd* weighted degrees on $R$, contradicting Lemma 7's even-iff-$R$
--   conclusion; $R' := \emptyset$ is forced.) Lemma 5 yields a weighting even on
--   $R$ with weighted degree $\alpha$ on $B$; the weighting lemma applied to $G[B]$
--   yields designated odd degrees $f$ on $B$, pairwise distinct on $B$-neighbors
--   (children `lemma_5_parity_subgraph`, `lemma_5_weight_reassignment`,
--   `lemma_5_parity_feasibility` -- queued). Since $R$ is independent,
--   $E(G) = E(B) \sqcup E(R,B)$, so the two weightings combine into a single
--   $\omega$ with even weighted degrees exactly on $R$ and odd, neighbor-distinct
--   degrees on $B$.
--
--   This node states that final transfer: from the combined engine output (a
--   $\{1,2,3\}$-weighting $\omega$ even on $R$, plus $f$ with $s_\omega = f$ odd
--   and neighbor-distinct on $B$) to Lemma 7's conclusion
--   (`7fd26f40-f4be-4ba9-b2c0-288a0592d592`): a vertex-coloring $\{1,2,3\}$-weighting
--   with $s_\omega(v)$ even iff $v \in R$. No flow machinery is used (the s-t
--   network belongs to Lemma 4), and Lemma 5's path refinement
--   (`lemma_5_path`, `ee289f01-40c5-4ad2-be91-c0ba55634423`) is not needed -- the
--   paper applies Lemma 5 "without considering any path $p$". Once the cited engine
--   children are proved, a PROVE worker assembles the combined $\omega$ and
--   discharges this node.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 8, proof of Lemma 7 (Lemma 5 application)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

/-- Lemma 7 from Lemma 5 (Keusch, arXiv:2303.02611v4, p. 8, proof of Lemma 7).

The paper applies Lemma 5 to the bipartite subgraph `G(R,B)` with `R' := ∅` and
`α` odd-valued on `B`; then `hpar` is exactly `|B|` even (a good-partition
hypothesis). Lemma 5 yields a weighting even on `R` with `wdeg = α` on `B`; the
weighting lemma on `G[B]` yields designated odd degrees `f` on `B`, distinct on
`B`-neighbors. Since `R` is independent, `E(G) = E(B) ⊔ E(R,B)`, and the two
weightings combine into one `ω` with even weighted degrees exactly on `R`. This
node is that final elementary transfer: from the combined engine output to
Lemma 7's conclusion. -/
theorem lemma_7_from_lemma5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (R B : Finset V)
    (hRB : IsGoodPartition G Finset.univ R B)
    (hengine : ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ R, Even (wdeg G ω v)) ∧
      ∃ f : V → ℕ, (∀ v ∈ B, wdeg G ω v = f v) ∧
        (∀ v ∈ B, Odd (f v)) ∧
        (∀ u v, u ∈ B → v ∈ B → G.Adj u v → f u ≠ f v)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω ∧
      ∀ v, Even (wdeg G ω v) ↔ v ∈ R := by sorry

end OneTwoThree.Weighting
