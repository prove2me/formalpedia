-- Prove2me | Theorems.Thm_ImpatientMatching_lemma_4_5
-- name    : ImpatientMatching.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:40.100128+00:00
-- url     : https://prove2.me/theorems/36b2f0a8-64e7-4b81-940e-ace63d792c19
-- title:
--   Lemma 4.5 — completing an occupied set: $\Phi(P)\ge\tau(H)$
-- statement:
--   Let $H$ be a finite simple graph. For every vertex set $P$,
--   $$\Phi(P)=|P|+u(P)\ge\tau(H),$$
--   where $u(P)$ is the number of edges of $H$ with no endpoint in $P$ and $\tau(H)$ is the minimum vertex-cover size.
--
--   This is the combinatorial link between occupied supplier queues and vertex covers in the upper bound.
--
--   Differences from the source:
--   - generalization: H is the cubic source graph → any finite simple graph; reason: cubicity is not used; a cubic graph is a special case
-- source:
--   C. Yan and S. M. Varma, Impatience Makes Matching NP-Hard, manuscript (sha256 7b1051b6c661435675185b0663cb08ab217698a2c4ee07fa0f473686dbb6bed9), Lemma 4.5, (18), p.13

import Definitions.Def_ImpatientMatching_Source

open NSWApxHard.Reduction

namespace ImpatientMatching

/-- **Lemma 4.5 (completing an occupied set).** Yan–Varma, manuscript (sha256 7b1051b6…), (18), p.13: for every `P ⊆ V_H`,
`Φ(P) = |P| + u(P) ≥ τ(H)`.

**Formalization Note.** Any finite simple graph: cubicity is not used. -/
theorem lemma_4_5 (H : GraphInput) (P : Finset (Fin H.N)) : tau H ≤ Phi H P := by sorry

end ImpatientMatching
