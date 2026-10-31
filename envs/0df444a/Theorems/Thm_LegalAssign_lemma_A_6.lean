-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_6
-- name    : LegalAssign.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:16.238987+00:00
-- url     : https://prove2.me/theorems/87b002f2-0a65-459d-926b-1ae01d1dfde9
-- title:
--   Lemma A.6 — $E(G_L)=\bigcup\{M:M\in\mathcal L\}$ at a fixed point
-- statement:
--   Let $k\in\mathbb N$ satisfy $\mathcal L^k=\mathcal L^{k+1}$, let $\mathcal L:=\mathcal L^k$, and let $G_L$ be the subgraph of $G$ induced by the edges $\bigcup\{M:M\in\mathcal M\setminus\mathcal I(\mathcal L)\}$. Then
--   $$E(G_L)=\bigcup\{M:M\in\mathcal L\}.$$
--
--   Together with Lemma A.3, this shows that the assignments of $\mathcal L$ use all and only the edges of $G_L$.
--
--   **Formalization Note** This $G_L$ is the graph of Appendix A; §3 defines it differently, and the statement here does not use the §3 graph.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - encoding: 𝓛 := 𝓛^k for k ∈ ℕ with 𝓛^k = 𝓛^{k+1} (Lemma A.1) → k : ℕ, including k = 0, with hypothesis legalSeq k = legalSeq (k + 1); reason: the statement is about any fixed index of the sequence; the source fixes the k given by Lemma A.1
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.6, p.27; footnote 2, p.27

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_legalSeq

namespace LegalAssign

/-- Lemma A.6 (arXiv:1809.08506v2, p.27). With `𝓛 := 𝓛^k` where `𝓛^k = 𝓛^{k+1}` and `G_L` the subgraph
with edges `⋃{M : M ∈ 𝓜 \ 𝓘(𝓛)}` (the definition of App. A, footnote 2): `E(G_L) = ⋃{M : M ∈ 𝓛}`. -/
theorem lemma_A_6 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (k : ℕ)
    (hk : G.legalSeq k = G.legalSeq (k + 1)) :
    edgeUnion (G.assignments \ G.blockedBy (G.legalSeq k)) = edgeUnion (G.legalSeq k) := by sorry

end LegalAssign
