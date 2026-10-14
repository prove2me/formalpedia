-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_5_parity_subgraph
-- name    : OneTwoThree.Weighting.lemma_5_parity_subgraph
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-12T00:06:27.582534+00:00
-- url     : https://prove2.me/theorems/fd865b10-ca13-4e19-9a5d-91d565fd33ba
-- title:
--   Lemma 5 parity subgraph — T-join with prescribed odd-degree vertex set
-- statement:
--   The T-join / parity-subgraph child of Lemma 5 (Keusch, *A Solution to the 1-2-3 Conjecture*, arXiv:2303.02611v4, p. 6, proof of Lemma 5, stage (a)).
--
--   The proof of Lemma 5 opens by fixing all edge weights at 2 and building a parity subgraph: given a connected graph G and a vertex set V_o of even cardinality (V_o := R' ∪ {v ∈ B : α(v) ≠ 2·deg(v)}, the vertices that must end with odd weighted degree), there is an edge set E_o such that the number of E_o-edges incident to v is odd exactly for v ∈ V_o. Keusch builds it by leaf induction in a spanning tree; no Mathlib spanning-tree or T-join API exists, so the eventual proof is elementary and inline (~150-250 lines).
--
--   The interface is deliberately Finset: the filter predicate (fun e => v ∈ e) is decidable via Sym2.Mem.decidable, and the edge-set inclusion is stated as (E_o : Set (Sym2 V)) ⊆ G.edgeSet since a bare Finset ⊆ against a Set fails typechecking. The parent's parity-feasibility node (Even #V_o) supplies the hypothesis; this node supplies the E_o interface consumed by the weight-reassignment child, and together they decompose OneTwoThree.Weighting.lemma_5 (18cd221d-d23a-4ae5-97c8-ca2db074a231), live-verified Open with deprecated_at=null immediately before posting.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 6, proof of Lemma 5 stage (a) (parity subgraph / T-join)

import Mathlib

namespace OneTwoThree.Weighting

theorem lemma_5_parity_subgraph {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (V_o : Finset V) (heven : Even (Finset.card V_o)) :
    ∃ E_o : Finset (Sym2 V),
      (E_o : Set (Sym2 V)) ⊆ G.edgeSet ∧
      ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔ v ∈ V_o := by sorry

end OneTwoThree.Weighting
