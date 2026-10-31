-- Prove2me | Theorems.Thm_LegalAssign_lemma_A_1
-- name    : LegalAssign.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:13.247754+00:00
-- url     : https://prove2.me/theorems/0f5d963e-2755-4317-a6eb-7dcfcc4bcfb5
-- title:
--   Lemma A.1 — the sequence $\mathcal L^i$ stabilizes
-- statement:
--   For the sequence $\mathcal L^0=\mathcal S(G,<,q)$, $\mathcal L^i=\mathcal L(\mathcal L^{i-1})$, there is $k\in\mathbb N$ with
--   $$\mathcal L^k=\mathcal L^{k+1}.$$
--
--   This produces the candidate for the unique legal set.
--
--   Differences from the source:
--   - encoding: <_v is a strict ordering of the neighbours of v in G → prefA a and prefB b are strict total orders on the whole other side; reason: only comparisons among neighbours ever enter, and every strict order on the neighbours extends to the whole side
--   - encoding: G is a bipartite graph, finite throughout the paper → Fintype A, Fintype B, E : Finset (A × B), assignments are Finsets of pairs; reason: Lean convention; the same instances
--   - reading: q = {q_b} ∈ ℕ^B, with no statement on whether this ℕ contains 0 → q : B → ℕ, so q_b = 0 is allowed; reason: the source does not settle it, and the Lean statement covers positive quotas and quota 0 alike
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, Lemma A.1, p.25

import Mathlib
import Definitions.Def_LegalAssign_Instance
import Definitions.Def_LegalAssign_legalSeq

namespace LegalAssign

/-- Lemma A.1 (arXiv:1809.08506v2, p.25): the sequence `𝓛^i` stabilizes. -/
theorem lemma_A_1 {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (G : Instance A B) :
    ∃ k, G.legalSeq k = G.legalSeq (k + 1) := by sorry

end LegalAssign
