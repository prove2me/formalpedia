-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_8
-- name    : LegalAssign.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:15.136784+00:00
-- url     : https://prove2.me/theorems/1972ed4b-80d5-4b64-b259-fe38b2235989
-- title:
--   Lemma A.8 — the fixed point $\mathcal L^k$ is the unique subset with the legal property
-- statement:
--   Let $k\in\mathbb N$ satisfy $\mathcal L^k=\mathcal L^{k+1}$, and let $\mathcal L:=\mathcal L^k$. Then $\mathcal L$ is the unique subset of $\mathcal M$ with the legal property: every $\mathcal L'\subseteq\mathcal M$ with the legal property equals $\mathcal L$.
--
--   This gives the uniqueness half of Theorem 3.3.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
--   - encoding: 𝓛 := 𝓛^k for k ∈ ℕ with 𝓛^k = 𝓛^{k+1} (Lemma A.1) → k : ℕ, including k = 0, with hypothesis legalSeq k = legalSeq (k + 1); reason: the statement is about any fixed index of the sequence; the source fixes the k given by Lemma A.1
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.8, p.28

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_legalSeq

namespace LegalAssign

/-- Lemma A.8 (arXiv:1809.08506v2, p.28): with `𝓛 := 𝓛^k` where `𝓛^k = 𝓛^{k+1}`, `𝓛` is the unique subset
of `𝓜` with the legal property. -/
theorem lemma_A_8 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) (k : ℕ)
    (hk : G.legalSeq k = G.legalSeq (k + 1)) (S : Set (Finset (A × B)))
    (hS : S ⊆ G.assignments) (hL : G.HasLegalProperty S) :
    S = G.legalSeq k := by sorry

end LegalAssign
