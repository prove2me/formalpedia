-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_8_v0_extension
-- name    : OneTwoThree.Weighting.lemma_8_v0_extension
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-11T12:22:19.766202+00:00
-- url     : https://prove2.me/theorems/ff98fd22-6843-478a-8a13-59025b240631
-- title:
--   Lemma 8 v₀-extension — the ω₃ v₀-edge weighting + conflict-repair step
-- statement:
--   The v₀-extension step of Keusch's Lemma 8 (A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, proof pp. 8–9).
--
--   Lemma 8's proof does NOT apply Lemma 7 to G[V∖{v₀}]. It re-runs the engine with v₀-aware inputs — Lemma 3 on G[B] with h(v) := 2|N(v)∖B|, Lemma 5 on the bipartite graph G(R,B) with R' := N(v₀)∩R and the two α-cases on N(v₀)∩B — and then extends the weighting to the v₀-incident edges in two elementary moves. This node isolates those two moves.
--
--   Hypotheses: the engine output on G[V∖{v₀}], formalized on G₀ := G.deleteIncidenceSet v₀ (SimpleGraph.deleteIncidenceSet: G with v₀'s incident edges removed — same edge set as the induced subgraph G[V∖{v₀}], vertex type V, so no subtype coercions): a {1,2,3}-weighting ω₁₂; designated odd colors f on B, pairwise distinct on B-neighbors; s_{ω₁₂} even on R exactly off N(v₀) (Lemma 5 (i)(ii) with R' = N(v₀)∩R); compensation weights c(v) ∈ {1,2,3} with s_{ω₁₂}(v) + c(v) = f(v) on N(v₀)∩B (and s_{ω₁₂} = f on B∖N(v₀)); and |N(v₀)∩R| + Σ_{v ∈ N(v₀)∩B} c(v) even — this evenness is what hpar buys in the paper (|N_R| even with all compensations 2, or |N_R| odd with one blue neighbor carrying an odd compensation in {1,3}). Plus lemma_8's own h2 (2 ≤ |N(v₀)∩R|), hpar, the good partition, and G[V∖{v₀}] connected.
--
--   Conclusion: a vertex-coloring {1,2,3}-weighting of G — lemma_8's conclusion (parent node OneTwoThree.Weighting.lemma_8, aaddfc19-dcf0-41a8-8dcd-fd1d40e9970f).
--
--   Proof idea (the paper's, pp. 8–9): (ω₃) put weight 1 on the v₀–R edges and c(v) on the v₀–B edges. Then s(v₀) is even by the evenness hypothesis; every red vertex is even again (odd + 1 on N(v₀)∩R, even elsewhere); every blue vertex attains its designated color f(v); since R is independent and f is odd/neighbor-distinct, the only possible coloring conflicts are between v₀ and its red neighbors. (Repair) write N(v₀)∩R = {v₁,…,v_k} with k ≥ 2 ordered by weighted degree; let x > 0 be smallest with s(v₀)+2x avoiding all s(vᵢ); raise selected v₀–R edge weights 1→3 (the paper's three cases on the position index) to get ω′ with s(v₀) distinct from every s(vᵢ) and no new conflicts. Finite parity/coloring case analysis on the edges v₀–N(v₀); no flow machinery. Sibling: lemma_7_from_lemma5 (6655c4ee-995d-496f-b728-21006c8f4542); lemma_5_path refinement d6776149-ae19-44e2-95f8-b7665a7474ce.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, Lemma 8 proof pp. 8-9 (v0-extension: ω3 construction + conflict repair)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

/-- Lemma 8 v₀-extension (Keusch, arXiv:2303.02611v4, Lemma 8 proof, pp. 8–9).

The paper proves Lemma 8 by re-running the engine on `G[V ∖ {v₀}]` (Lemma 3 on
`G[B]` with `h(v) := 2|N(v) ∖ B|`, Lemma 5 on `G(R,B)` with `R' := N(v₀) ∩ R`
and the two `α`-cases on `N(v₀) ∩ B`) and then extending the weighting to the
`v₀`-incident edges. This node is that extension step: `ω₃` (weight `1` on the
`v₀`–`R` edges, compensation weights `c` on the `v₀`–`B` edges, making `s(v₀)`
even) followed by the conflict repair (order `N(v₀) ∩ R` by weighted degree,
raise selected `v₀`–`R` edge weights `1 → 3` in the paper's three cases).
`G.deleteIncidenceSet v₀` is the edge-deletion form of `G[V ∖ {v₀}]` (same edge
set, vertex type `V`). -/
theorem lemma_8_v0_extension {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v₀ : V) (hconn : (G.induce ({v₀}ᶜ : Set V)).Connected)
    (R B : Finset V) (hRB : IsGoodPartition G {v₀}ᶜ R B)
    (hengine : ∃ ω₁₂ : Sym2 V → ℕ, ∃ f : V → ℕ, ∃ c : V → ℕ,
      IsWeighting (G.deleteIncidenceSet v₀) 3 ω₁₂ ∧
      (∀ v ∈ B, Odd (f v)) ∧
      (∀ u v, u ∈ B → v ∈ B → (G.deleteIncidenceSet v₀).Adj u v → f u ≠ f v) ∧
      (∀ v ∈ R, Even (wdeg (G.deleteIncidenceSet v₀) ω₁₂ v) ↔ v ∉ G.neighborFinset v₀) ∧
      (∀ v ∈ B, v ∉ G.neighborFinset v₀ → wdeg (G.deleteIncidenceSet v₀) ω₁₂ v = f v) ∧
      (∀ v ∈ B, v ∈ G.neighborFinset v₀ →
        c v ∈ Finset.Icc 1 3 ∧ wdeg (G.deleteIncidenceSet v₀) ω₁₂ v + c v = f v) ∧
      Even (Finset.card (G.neighborFinset v₀ ∩ R) +
        Finset.sum (G.neighborFinset v₀ ∩ B) fun v => c v))
    (h2 : 2 ≤ Finset.card (G.neighborFinset v₀ ∩ R))
    (hpar : Even (Finset.card (G.neighborFinset v₀ ∩ R)) ∨
      1 ≤ Finset.card (G.neighborFinset v₀ ∩ B)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧ IsVertexColoring G ω := by sorry

end OneTwoThree.Weighting
