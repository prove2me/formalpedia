-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_Supplement_lemma_7
-- name    : NetworkSumSecure.Solvability.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:08:37.574338+00:00
-- url     : https://prove2.me/theorems/3fecda7f-a8f8-4531-ae5b-23568955784a
-- title:
--   Lemma 7 — server column rank lower bound
-- statement:
--   Fix a finite directed acyclic multigraph network $N$ satisfying the published model assumptions, a finite field $F$, a security level $r\in\mathbb N$, and a private-key assignment $z:U\to\mathbb N$. Let $C$ be any scalar linear causal local code with exactly this assignment and let $\varphi$ be any linear server decoder. If the resulting scheme is feasible (correct and sum-secure), then
--
--   $$
--   \operatorname{Rank}(G_\rho)\ge r+1,\qquad
--   G_\rho=[g_e:e\in\operatorname{In}(\rho)].
--   $$
--
--   Here $g_e$ is the global encoding column induced by the actual local execution on edge $e$, and rank is the dimension over $F$ of the span of those columns. This necessary condition supports the private-key characterization in Theorem 2. It holds over every finite field, including fields smaller than the construction threshold.
--
--   **Formalization Note** The statement uses the published `Feasible`, `globalColumn`, `columnRank`, and `incoming` without alteration. The private-key coordinates remain in the published user-block order.
--
--   Differences from the source:
--   - generalization: the standing convention assumes a sufficiently large finite field → the necessary conclusion also holds over every finite field without a cardinality hypothesis; reason: the necessity proof uses only correctness, exact sum-security, and finite-dimensional linear algebra; it does not use either field-size estimate (34) or (53)
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 18, Lemma 7 (PDF p. 20).

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_algebra

namespace NetworkSumSecure.Solvability.Supplement

/-- Lemma 7, printed p.18 (PDF 20). No lower bound on the finite field size. -/
theorem lemma_7 {V E U F : Type} [Fintype V] [Fintype E] [Fintype U]
    [Field F] [Fintype F] (N : Network V E U) (r : ℕ) (z : U → ℕ)
    (C : LocalCode N F z) (φ : Decoder N F) (h : Feasible C φ r) :
    r + 1 ≤ columnRank (globalColumn C) (incoming N N.server) := by sorry

end NetworkSumSecure.Solvability.Supplement
