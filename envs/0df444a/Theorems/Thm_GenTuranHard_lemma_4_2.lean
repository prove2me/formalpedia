-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_2
-- name    : GenTuranHard.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:35.101325+00:00
-- url     : https://prove2.me/theorems/a5695084-d3cf-4638-b766-814e087f7f7a
-- title:
--   Lemma 4.2 — $v(Q_I) \le v(Q)$ and $Q_I$ is bipartite
-- statement:
--   Let $Q$ be a bipartite graph and $I$ an independent set of $Q$. Then
--
--   1. $v(Q_I) \le v(Q)$;
--   2. $Q_I$ is bipartite.
--
--   Hence every terminal graph of the expansion of Lemma 4.3 is bipartite with at most $v(T)$ vertices.
--
--   Differences from the source:
--   - encoding: Q, G arbitrary finite graphs → graphs on Fin n (FinGraph); reason: every finite graph is isomorphic to one on {0,…,n−1}; every quantity involved is isomorphism-invariant
--   - encoding: the vertices of Q_I (classes of V(Q)∖I and new isolated vertices v′) → quotGraph Q I renumbered on Fin v(Q_I) by a fixed bijection; reason: homomorphism counts, vertex counts, p(·), edges and bipartiteness do not depend on the numbering
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.2, p.13

import Mathlib
import Definitions.Def_GenTuranHard_quotGraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.2** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.2, p.13). Let `Q`
be a bipartite graph and `I` an independent set of `Q`. Then (i) `v(Q_I) ≤ v(Q)`, and (ii) `Q_I` is
bipartite.

**Formalization Note** `Q` is a finite graph on `Fin _`; `Q_I` is `quotGraph`. Bipartite is Mathlib's
`IsBipartite` (2-colorable). -/
theorem lemma_4_2 (Q : FinGraph) (hQ : Q.2.IsBipartite) (I : Finset (Fin Q.1))
    (hI : Q.2.IsIndepSet (I : Set (Fin Q.1))) :
    (quotGraph Q I).1 ≤ Q.1 ∧ (quotGraph Q I).2.IsBipartite := by sorry

end GenTuranHard
