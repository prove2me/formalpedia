-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_4
-- name    : GenTuranHard.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:44.695196+00:00
-- url     : https://prove2.me/theorems/e8297eb3-94fd-4869-b322-a42ceba135c7
-- title:
--   Lemma 4.4 — $p(Q_I) \le p(Q)$, strictly for a largest $I$ with $e(Q_I) > 0$ when $p(Q) \ge 3$
-- statement:
--   Let $Q$ be a bipartite graph and $p(Q)$ its number of nonisolated vertices.
--
--   1. For any independent set $I$, $p(Q_I) \le p(Q)$.
--   2. Suppose that $p(Q) \ge 3$. If $I$ is an independent set of maximum cardinality subject to $e(Q_I) > 0$, then $p(Q_I) < p(Q)$.
--
--   Repeated along a sequence of (4.1), the second part forces the number of nonisolated vertices down to $2$ (Lemma 4.5).
--
--   Differences from the source:
--   - encoding: Q, G arbitrary finite graphs → graphs on Fin n (FinGraph); reason: every finite graph is isomorphic to one on {0,…,n−1}; every quantity involved is isomorphism-invariant
--   - encoding: the vertices of Q_I (classes of V(Q)∖I and new isolated vertices v′) → quotGraph Q I renumbered on Fin v(Q_I) by a fixed bijection; reason: homomorphism counts, vertex counts, p(·), edges and bipartiteness do not depend on the numbering
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.4, p.14

import Mathlib
import Definitions.Def_GenTuranHard_quotGraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 4.4** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.4, p.14). Let `Q`
be a bipartite graph. (i) For any independent set `I`, `p(Q_I) ≤ p(Q)`. (ii) Suppose `p(Q) ≥ 3`. If `I`
is an independent set of maximum cardinality subject to `e(Q_I) > 0`, then `p(Q_I) < p(Q)`.

**Formalization Note** `p(·)` is `pNon` (the number of nonisolated vertices); `e(Q_I) > 0` is
nonemptiness of the edge set. `Q` is a finite graph on `Fin _`. -/
theorem lemma_4_4 (Q : FinGraph) (hQ : Q.2.IsBipartite) :
    (∀ I : Finset (Fin Q.1), Q.2.IsIndepSet (I : Set (Fin Q.1)) → pNon (quotGraph Q I) ≤ pNon Q) ∧
      (3 ≤ pNon Q → ∀ I : Finset (Fin Q.1), Q.2.IsIndepSet (I : Set (Fin Q.1)) →
        (quotGraph Q I).2.edgeSet.Nonempty →
        (∀ J : Finset (Fin Q.1), Q.2.IsIndepSet (J : Set (Fin Q.1)) →
          (quotGraph Q J).2.edgeSet.Nonempty → J.card ≤ I.card) →
        pNon (quotGraph Q I) < pNon Q) := by sorry

end GenTuranHard
