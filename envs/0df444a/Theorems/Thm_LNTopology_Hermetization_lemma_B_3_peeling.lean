-- Prove2me | Theorems.Thm_LNTopology_Hermetization_lemma_B_3_peeling
-- name    : LNTopology.Hermetization.lemma_B_3_peeling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:28:55.101648+00:00
-- url     : https://prove2.me/theorems/1162adbe-c72c-44f7-8d09-042448d0c476
-- title:
--   Lemma B.3: peeling finds a subgraph of large minimum degree in $O(V+E)$
-- statement:
--   There is a constant $C$ such that the following holds for every $n$, every family of adjacency lists $\mathrm{adj}$ on the vertices $\{0,\dots,n-1\}$ and every decidable degree test $\mathrm{bad}$ on natural numbers. Let $H$ be the vertex set returned by the peeling algorithm. Then:
--
--   1. the algorithm makes at most
--   $$C\Bigl(n+\sum_{v}|\mathrm{adj}(v)|+1\Bigr)$$
--   ticks, that is, it runs in time $O(V+E)$;
--   2. if the lists are the adjacency lists of a simple graph and the test is downward closed ($\mathrm{bad}(b)$ and $a\le b$ imply $\mathrm{bad}(a)$), then no vertex of $H$ has a bad degree in $H$, and $H$ is nonempty if and only if some nonempty vertex set $W$ has no vertex with a bad degree in $W$.
--
--   With the test "degree $<\tau$" for $\tau=g_+^{-1}(2\,\mathrm{disc}(G))$ this is Lemma B.3: the algorithm finds a subgraph $H$ with $\delta(H)\ge\tau$ if one exists, and otherwise returns the empty graph, in time $O(V+E)$. Theorem 3.8 runs it to locate the dense core produced by Lemma B.4.
--
--   **Formalization Note** Running time is the tick count of the mission's real-RAM model. The paper's proof deletes vertices of degree $\le\tau$, which would miss a subgraph with $\delta(H)=\tau$; the algorithm here deletes exactly the vertices whose degree fails the test.
--
--   Differences from the source:
--   - generalization: the degree test "degree ≥ g₊⁻¹(2disc(G))" → any downward-closed degree test bad; reason: Lemma B.3 is the instance bad d := d < g₊⁻¹(2disc(G)), which is downward closed
--   - generalization: running time O(V + E) for a graph → the tick bound holds for every family of lists, well formed or not; correctness for well-formed lists; reason: well-formed lists are exactly the graphs, so this specializes to the printed bound
--   - reading: running time O(V + E) → adjacency lists, at most C(n + Σ_v |adj v| + 1) ticks with C chosen before the input; reason: O(V + E) presupposes adjacency lists (Σ_v |adj v| = 2|E|); with an adjacency matrix it is unattainable
--   - encoding: the printed algorithm deletes vertices of degree ≤ g₊⁻¹(2disc(G)) → peel deletes the vertices whose degree fails the test (degree < τ for Lemma B.3); reason: the lemma is existential; the printed comparison misses H with δ(H) = τ (K₄ with τ = 3), the algorithm here is the paper's with the comparison matching its claim
--   - encoding: a subgraph H, or the empty graph → the vertex set H of an induced subgraph, nonempty iff a nonempty W with no bad degree exists; reason: a subgraph on W with large minimum degree exists iff the induced one does
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Lemma B.3 and its proof, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_WellFormedAdj
import Definitions.Def_LNTopology_Hermetization_listDegIn
import Definitions.Def_LNTopology_Hermetization_peel

namespace LNTopology.Hermetization

/-- **Lemma B.3 (peeling finds a subgraph of large minimum degree in linear time).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Lemma B.3, p. 12: "There is an algorithm that, given a graph G, finds a subgraph H with
δ(H) ≥ g₊⁻¹(2disc(G)), if there exists one, or alternatively returns an empty graph if there is
no such H. The running time of the algorithm is O(V + E)."

There is a constant `C` such that for every graph on `Fin n` given by adjacency lists `adj` and
every degree test `bad`, the algorithm `peel` runs in at most `C · (n + Σ_v |adj v| + 1)` ticks,
and, when the lists are well formed and `bad` is downward closed, its output `H`
* has no vertex whose degree in `H` is bad, and
* is nonempty if and only if some nonempty vertex set `W` has no vertex whose degree in `W` is
  bad.

**Formalization Note.** Generalization G3: the paper's test is "degree `< τ`" with
`τ = g₊⁻¹(2disc(G))`, the instance `bad d := (d : ℝ) < τ` (downward closed); any downward
closed test is allowed. Reading R5: `O(V + E)` on adjacency lists, `C` chosen before the input,
and the time bound holds on every input. Encoding E1: the printed proof deletes degree `≤ τ`,
which misses `H` with `δ(H) = τ`; `peel` deletes exactly the bad degrees. -/
theorem lemma_B_3_peeling :
    ∃ C : ℕ, ∀ (n : ℕ) (adj : Fin n → List (Fin n)) (bad : ℕ → Prop) [DecidablePred bad],
      ((peel adj bad).run 0).2 ≤ C * (n + ∑ v, (adj v).length + 1) ∧
      (WellFormedAdj adj → (∀ a b : ℕ, a ≤ b → bad b → bad a) →
        (∀ v ∈ ((peel adj bad).run 0).1,
            ¬ bad (listDegIn adj ((peel adj bad).run 0).1 v)) ∧
        ((∃ W : Finset (Fin n), W.Nonempty ∧ ∀ v ∈ W, ¬ bad (listDegIn adj W v)) ↔
          ((peel adj bad).run 0).1.Nonempty)) := by sorry

end LNTopology.Hermetization
