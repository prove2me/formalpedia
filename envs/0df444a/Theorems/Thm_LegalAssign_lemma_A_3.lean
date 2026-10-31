-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_3
-- name    : LegalAssign.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:21.154545+00:00
-- url     : https://prove2.me/theorems/4ea71f48-2fed-4549-8422-9de91c36ec49
-- title:
--   Lemma A.3 — a fixed point of $\mathcal L$ is the stable set of a subinstance
-- statement:
--   Let $\mathcal M=\mathcal M(G,q)$ and let $\mathcal M_0\subseteq\mathcal M$ satisfy $\mathcal L(\mathcal M_0)=\mathcal M_0$. Then
--   $$\mathcal M_0=\mathcal S(G',<,q),\qquad\text{where } G':=G[E'],\quad E':=\bigcup\{M:M\in\mathcal M\setminus\mathcal I(\mathcal M_0)\}.$$
--
--   This is where the classical theory of stable assignments enters the study of the operator $\mathcal L$.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.3, p.26

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_legalSeq

namespace LegalAssign

/-- Lemma A.3 (arXiv:1809.08506v2, p.26): a fixed point `𝓜₀ ⊆ 𝓜` of `𝓛` is `𝓢(G', <, q)`, where
`G' := G[E']` and `E' := ⋃{M : M ∈ 𝓜 \ 𝓘(𝓜₀)}`. -/
theorem lemma_A_3 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (S : Set (Finset (A × B)))
    (hS : S ⊆ G.assignments) (hfix : G.legalOp S = S) :
    S = (G.restrict (edgeUnion (G.assignments \ G.blockedBy S))).stable := by sorry

end LegalAssign
