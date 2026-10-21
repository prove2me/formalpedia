-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_corollary_3_8
-- name    : ImprovedMMS.Additive.corollary_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:21.618711+00:00
-- url     : https://prove2.me/theorems/edad8d12-535d-4b87-80c2-d81f48e33871
-- title:
--   Corollary 3.8, p. 19 — after removing F_H(M, X̂) and its neighbours, F_{H′}(M′, X̂′) = ∅
-- statement:
--   Let $H$ be a bipartite graph with sides $\hat{\mathcal X}$, $\hat{\mathcal Y}$ and let $M$ be a maximum matching of $H$. Let $H'$ be the sub-graph of $H$ induced on $\hat{\mathcal X}'\cup\hat{\mathcal Y}'$, where
--   $$\hat{\mathcal X}'=\hat{\mathcal X}\setminus F_H(M,\hat{\mathcal X}),\qquad \hat{\mathcal Y}'=\hat{\mathcal Y}\setminus N\big(F_H(M,\hat{\mathcal X})\big).$$
--   Then $F_{H'}(M',\hat{\mathcal X}')=\emptyset$ for every maximum matching $M'$ of $H'$.
--
--   The paper applies it to the value graph to separate the goods that can be matched with room to spare from the rest.
--
--   **Formalization Note** $H'$ has edge set `inducedEdges E X' Y'`, the edges of $H$ with both ends in $\hat{\mathcal X}'\cup\hat{\mathcal Y}'$. Edges of $H$ satisfy $E\subseteq\hat{\mathcal X}\times\hat{\mathcal Y}$.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 19, Corollary 3.8 (of Lemmas 3.7 and 3.6)

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

namespace ImprovedMMS.Additive

/-- Corollary 3.8 (p. 19): let `Mt` be a maximum matching of the bipartite graph `H` with sides
`X`, `Y` and edges `E ⊆ X × Y`, and let `H'` be the sub-graph induced on `X' = X \ F_H(Mt, X)` and
`Y' = Y \ N(F_H(Mt, X))`. Then `F_{H'}(M', X') = ∅` for every maximum matching `M'` of `H'`. -/
theorem corollary_3_8 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    ∀ M' : Finset (α × β),
      IsMaxMatching (inducedEdges E (X \ FH E Mt X Y) (Y \ nbhd E (FH E Mt X Y))) M' →
      FH (inducedEdges E (X \ FH E Mt X Y) (Y \ nbhd E (FH E Mt X Y))) M'
        (X \ FH E Mt X Y) (Y \ nbhd E (FH E Mt X Y)) = ∅ := by sorry

end ImprovedMMS.Additive
