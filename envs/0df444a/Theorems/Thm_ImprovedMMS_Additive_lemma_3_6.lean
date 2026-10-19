-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_6
-- name    : ImprovedMMS.Additive.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:21.004593+00:00
-- url     : https://prove2.me/theorems/8a37298d-47c0-40a0-b2cc-7834c76789a6
-- title:
--   Lemma 3.6, p. 19 — every non-empty T ⊆ X̂ \ F_H(M, X̂) has |N(T)| > |T|
-- statement:
--   Let $H$ be a bipartite graph with sides $\hat{\mathcal X}$, $\hat{\mathcal Y}$ and let $M$ be a maximum matching of $H$. Then for every non-empty set $T\subseteq\hat{\mathcal X}\setminus F_H(M,\hat{\mathcal X})$,
--   $$|N(T)|>|T|,$$
--   where $N(T)$ is the set of neighbours of $T$.
--
--   Together with Lemma 3.7 it gives Corollary 3.8, which the paper uses to split agents and goods into clusters.
--
--   **Formalization Note** The page says "for every set $T$"; at $T=\emptyset$ the inequality $0>0$ fails, so $T$ is non-empty. Edges satisfy $E\subseteq\hat{\mathcal X}\times\hat{\mathcal Y}$.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 19, Lemma 3.6 (F_H: Definition 3.5, p. 18)

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

namespace ImprovedMMS.Additive

/-- Lemma 3.6 (p. 19): for a bipartite graph with sides `X`, `Y`, edges `E ⊆ X × Y` and a maximum
matching `Mt`, every non-empty `T ⊆ X \ F_H(Mt, X)` has `|N(T)| > |T|`. -/
theorem lemma_3_6 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    ∀ T ⊆ X \ FH E Mt X Y, T.Nonempty → T.card < (nbhd E T).card := by sorry

end ImprovedMMS.Additive
