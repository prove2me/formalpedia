-- Prove2me | Theorems.Thm_LefebvreVariations_connected_subgraph_count_le_three
-- name    : LefebvreVariations.connected_subgraph_count_le_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:50.412808+00:00
-- url     : https://prove2.me/theorems/53399258-c2a0-5653-977c-acd2fc82e101
-- title:
--   Lefebvre's variations, No. 197 — on a theme by Balasubramanian, Davydova and Lin: counting connected vertex sets that meet a given set, for sets of at most three vertices
-- statement:
--   Let $G$ be a finite simple graph of maximum degree at most $\Delta$, let $V_2$ be a set of vertices, and let $m\le 3$. Then
--   $$
--   \#\bigl\{\,S\subseteq V : |S|=m,\ S\cap V_2\neq\emptyset,\ G[S]\text{ connected}\,\bigr\}\ \le\ |V_2|\,(\Delta+1)^{2m}.
--   $$
--
--   For general $m$ this is the counting lemma used for witness subgraphs in the analysis of a passive self-correcting quantum memory (a witness subgraph is a connected induced subgraph of the decoding graph meeting a distinguished vertex set); the platform lists it as open for all $m$. The cases $m\le3$ are the smallest ones; for $m=0$ the count is $0$, for $m=1$ it is $|V_2|$.
--
--   **Formalization Note** `G : SimpleGraph V` on a finite type `V` with decidable adjacency, `hΔ : ∀ v, G.degree v ≤ Δ`, sets are `Finset V`, and connectivity is `(G.induce (S : Set V)).Connected`. The only change from the platform statement is the added hypothesis `m ≤ 3`. `Δ = 0` is allowed.
--
--   **Why this is a variation.** A variation on the open platform problem SelfCorrect3D.Memory.connected_subgraph_count (the number of m-element connected vertex sets meeting V_2 is at most |V_2|(Delta+1)^(2m)), played at m <= 3 with the parent's formula copied verbatim. The statement for all m remains open on the platform.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The general lemma is Lemma 5.9 of Balasubramanian, Davydova and Lin, A passive self-correcting quantum memory in three dimensions (arXiv:2605.10943), cited as recorded by the platform and not read. The cases m <= 3 were checked by brute force over every simple graph on at most 6 vertices, every vertex set V_2 and m = 1, 2, 3 (6393054 instances, no violation).

import Mathlib

namespace LefebvreVariations

open Classical in
/-- Counting connected witness sets, at the first sizes `m ≤ 3`: in a finite simple graph of
maximum degree at most `Δ`, the number of `m`-element vertex sets `S` that meet a given vertex set
`V₂` and induce a connected subgraph is at most `|V₂| (Δ + 1)^{2m}`. For general `m` this is the
counting lemma used for witness subgraphs in the analysis of self-correcting quantum memories; here
only `m = 0, 1, 2, 3` is claimed. A brute-force count over every graph on at most `6` vertices, every
`V₂` and `m = 1, 2, 3` found no violation; `m = 0` is empty because `S ∩ V₂` must be nonempty. -/
theorem connected_subgraph_count_le_three {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ)
    (V₂ : Finset V) (m : ℕ) (hm : m ≤ 3) :
    (Finset.univ.filter fun S : Finset V =>
        S.card = m ∧ (S ∩ V₂).Nonempty ∧ (G.induce (S : Set V)).Connected).card ≤
      V₂.card * (Δ + 1) ^ (2 * m) := by
  sorry

end LefebvreVariations
