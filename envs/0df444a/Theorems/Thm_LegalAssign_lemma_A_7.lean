-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_7
-- name    : LegalAssign.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:47.320844+00:00
-- url     : https://prove2.me/theorems/7bb1ea1e-d5f1-42e0-a8eb-07397c15939b
-- title:
--   Lemma A.7 — the fixed point $\mathcal L^k$ has the legal property
-- statement:
--   Let $k\in\mathbb N$ satisfy $\mathcal L^k=\mathcal L^{k+1}$, and let $\mathcal L:=\mathcal L^k$. Then $\mathcal L\subseteq\mathcal M$ has the legal property, that is,
--   $$\mathcal I(\mathcal L)=\mathcal M\setminus\mathcal L.$$
--
--   This gives the existence half of Theorem 3.3.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - encoding: 𝓛 := 𝓛^k for k ∈ ℕ with 𝓛^k = 𝓛^{k+1} (Lemma A.1) → k : ℕ, including k = 0, with hypothesis legalSeq k = legalSeq (k + 1); reason: the statement is about any fixed index of the sequence; the source fixes the k given by Lemma A.1
--   - encoding: 𝓛 ⊆ 𝓜 is left implicit → stated as a conjunct of the conclusion; reason: the legal property is defined for subsets of 𝓜, and legalSeq k is a set of finsets a priori
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.7, p.28

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_legalSeq

namespace LegalAssign

/-- Lemma A.7 (arXiv:1809.08506v2, p.28): with `𝓛 := 𝓛^k` where `𝓛^k = 𝓛^{k+1}`, `𝓘(𝓛) = 𝓜 \ 𝓛`. -/
theorem lemma_A_7 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (k : ℕ)
    (hk : G.legalSeq k = G.legalSeq (k + 1)) :
    G.legalSeq k ⊆ G.assignments ∧ G.HasLegalProperty (G.legalSeq k) := by sorry

end LegalAssign
