-- Prove2me | Theorems.Thm_GenTuranHard_lemma_4_1
-- name    : GenTuranHard.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:22.596207+00:00
-- url     : https://prove2.me/theorems/8e669e57-f2da-4a6a-8c41-0d2feee0523a
-- title:
--   Lemma 4.1 — $\hom(Q, L_x(G)) = \sum_{I \text{ independent}} x^{|I|} \hom(Q_I, G)$
-- statement:
--   For any graph $G$, bipartite graph $Q$ and positive integer $x$,
--
--   $$
--   \hom(Q, L_x(G)) = \sum_{\substack{I \subseteq V(Q) \\ I \text{ independent}}} x^{|I|} \hom(Q_I, G).
--   $$
--
--   A homomorphism into $L_x(G)$ is determined by the set $I$ of vertices sent to leaves, a homomorphism of $Q_I$ into $G$, and the choice of one of the $x$ leaves for each vertex of $I$. Iterated, this gives the expansion of Lemma 4.3.
--
--   Differences from the source:
--   - encoding: Q, G arbitrary finite graphs → graphs on Fin n (FinGraph); reason: every finite graph is isomorphic to one on {0,…,n−1}; every quantity involved is isomorphism-invariant
--   - encoding: the vertices of Q_I (classes of V(Q)∖I and new isolated vertices v′) → quotGraph Q I renumbered on Fin v(Q_I) by a fixed bijection; reason: homomorphism counts, vertex counts, p(·), edges and bipartiteness do not depend on the numbering
--   - encoding: L_x(G), G with x leaves attached to every vertex → leafAdd x G on Fin (n + n·x): G on 0, …, n−1, the j-th leaf of the anchor v is n + v·x + j; reason: one numbering of the vertex set; homomorphism counts do not depend on it
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 4.1, p.13

import Mathlib
import Definitions.Def_GenTuranHard_leafAdd
import Definitions.Def_GenTuranHard_quotGraph

set_option autoImplicit false

namespace GenTuranHard

open scoped Classical in
/-- **Lemma 4.1** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 4.1, p.13). For any
graph `G`, bipartite graph `Q` and positive integer `x`,
`hom(Q, L_x(G)) = Σ_{I ⊆ V(Q) independent} x^{|I|} hom(Q_I, G)`.

**Formalization Note** `Q` and `G` are finite graphs on `Fin _` (every finite graph is isomorphic to
one); `Q_I` is `quotGraph` and `L_x(G)` is `leafAdd`. -/
theorem lemma_4_1 (G Q : FinGraph) (hQ : Q.2.IsBipartite) (x : ℕ) (hx : 0 < x) :
    homCount Q.2 (leafAdd x G).2 =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin Q.1))).filter
          (fun I : Finset (Fin Q.1) => Q.2.IsIndepSet (↑I : Set (Fin Q.1))),
        x ^ Finset.card I * homCount (quotGraph Q I).2 G.2 := by sorry

end GenTuranHard
