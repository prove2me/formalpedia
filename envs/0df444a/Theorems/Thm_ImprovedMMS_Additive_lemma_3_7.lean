-- Prove2me | Theorems.Thm_ImprovedMMS_Additive_lemma_3_7
-- name    : ImprovedMMS.Additive.lemma_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:25.532824+00:00
-- url     : https://prove2.me/theorems/3a046006-ee53-4fc2-8afa-f527a43455a3
-- title:
--   Lemma 3.7, p. 19 — F_H(M, X̂) = ∅ iff |N(T)| > |T| for every non-empty T ⊆ X̂
-- statement:
--   Let $H$ be a bipartite graph with sides $\hat{\mathcal X}$, $\hat{\mathcal Y}$ and let $M$ be a maximum matching of $H$. Then
--   $$F_H(M,\hat{\mathcal X})=\emptyset\iff |N(T)|>|T|\ \text{ for every non-empty } T\subseteq\hat{\mathcal X}.$$
--
--   It characterises when the set $F_H$ of Definition 3.5 vanishes by a strict Hall condition.
--
--   **Formalization Note** As printed ("for all $T\subseteq\hat{\mathcal X}$") the right side fails at $T=\emptyset$ in every graph, so the lemma would be false whenever $F_H=\emptyset$; $T$ is non-empty. $M$ is a maximum matching, as Definition 3.5 requires for $F_H(M,\hat{\mathcal X})$. Edges satisfy $E\subseteq\hat{\mathcal X}\times\hat{\mathcal Y}$.
-- source:
--   Ghodsi, Hajiaghayi, Seddighin, Seddighin & Yami, Fair Allocation of Indivisible Goods: Improvement and Generalization, arXiv:1704.00222v3, p. 19, Lemma 3.7 (F_H: Definition 3.5, p. 18)

import Mathlib
import Definitions.Def_ImprovedMMS_Additive_Bipartite

namespace ImprovedMMS.Additive

/-- Lemma 3.7 (p. 19): for a bipartite graph with sides `X`, `Y`, edges `E ⊆ X × Y` and a maximum
matching `Mt`, `F_H(Mt, X) = ∅` iff every non-empty `T ⊆ X` has `|N(T)| > |T|`. -/
theorem lemma_3_7 {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (Y : Finset β) (E : Finset (α × β)) (hE : E ⊆ X ×ˢ Y)
    (Mt : Finset (α × β)) (hM : IsMaxMatching E Mt) :
    FH E Mt X Y = ∅ ↔ ∀ T ⊆ X, T.Nonempty → T.card < (nbhd E T).card := by sorry

end ImprovedMMS.Additive
