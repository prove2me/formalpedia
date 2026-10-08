-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_lemma_5
-- name    : NashWilliams61.TreePacking.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:53.747241+00:00
-- url     : https://prove2.me/theorems/0fdbb0f7-518e-4191-8494-1428c1c86aca
-- title:
--   Lemma 5 — a critical graph is admissible iff $\Delta_G(X) \ge 0$ for every non-empty $X$
-- statement:
--   Let $G$ be a finite multigraph without loops on vertex set $V$, $k \ge 1$, and suppose $G$ is critical: $|E(G)| = k(|V| - 1)$. Then $G$ is admissible (every partition $P$ of $V$ has $|E_P(G)| \ge k(|P| - 1)$) if and only if
--   $$\Delta_G(X) = k(|X| - 1) - e_X \ge 0 \quad \text{for every non-empty } X \subseteq V .$$
--
--   For critical graphs this replaces the partition condition (1) by a condition on single vertex sets, which is the form the couples of Lemma 3 work with.
--
--   **Formalization Note** Criticality and $\Delta_G$ are in $\mathbb Z$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 448, Lemma 5

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Lemma 5** (Nash-Williams 1961, p. 448). A critical graph `G` is admissible if and only
if `Δ_G(X) ≥ 0` for every non-empty subset `X` of `V(G)`. -/
theorem lemma_5 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (hcrit : IsCritical k ends) :
    IsAdmissible k ends ↔ ∀ X : Finset V, X.Nonempty → 0 ≤ Delta k ends X := by sorry

end NashWilliams61.TreePacking
