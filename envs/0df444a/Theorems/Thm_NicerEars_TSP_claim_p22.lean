-- Prove2me | Theorems.Thm_NicerEars_TSP_claim_p22
-- name    : NicerEars.TSP.claim_p22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:56.211083+00:00
-- url     : https://prove2.me/theorems/f3558e29-3d1c-49d2-ac70-66e17c711cc3
-- title:
--   Proof of Theorem 29, p. 22, Claim — a tour with at most 7/5 Λ(G′, M) edges
-- statement:
--   **Claim** (proof of Theorem 29). Let $G'$ be a graph with a nice ear-decomposition without 1-ears that contains a maximum earmuff for the eardrum $M$ associated with it and $T=\emptyset$. Then $G'$ has a tour of cardinality at most
--
--   $$\tfrac75\,\Lambda(G',M),\qquad \Lambda(G',M)=\tfrac23L_\mu(G',M)+\tfrac13L_\varphi(G'),$$
--
--   where $L_\mu(G',M)=|V(G')|-1+|M|-\mu(G',M)$ and $L_\varphi(G')=|V(G')|+\varphi(G')-1$.
--
--   The Claim balances the two tour constructions (Theorem 24 and Lemma 28) at $\pi=\frac1{10}\Lambda$, where both give $\frac75\Lambda$; Theorem 29 follows because $\Lambda\le\mathrm{LP}(G)$ and deleting 1-ears does not change $\Lambda$.
--
--   **Formalization Note.** $G'$ is an arbitrary graph with the stated ear-decomposition, as on the page; it need not be 2-vertex-connected. "Without 1-ears" means every ear has length at least 2. The $O(|V(G')|^3)$ construction time is not formalized.
-- source:
--   Sebő and Vygen, Shorter tours by nicer ears, arXiv:1201.1870v3, p. 22, proof of Theorem 29, Claim

import Mathlib
import Definitions.Def_NicerEars_TSP_Earmuff

namespace NicerEars.TSP

open Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proof of Theorem 29, p. 22, Claim: a graph G′ with a nice ear-decomposition without 1-ears,
containing a maximum earmuff for the eardrum M associated with it and T = ∅, has a tour of
cardinality at most 7/5 Λ(G′, M), where Λ(G′, M) = ⅔ L_µ(G′, M) + ⅓ L_ϕ(G′). -/
theorem claim_p22 (G' : Graph V E) (D : EarDecomposition G') (hnice : D.IsNice)
    (hD : ∀ i, (D.ear i).IsNontrivial) (hmax : D.ContainsMaxEarmuff ∅) :
    ∃ F : Finset (E × Fin 2), G'.IsTour F ∧
      (#F : ℝ) ≤ 7 / 5 * G'.Lambda (D.eardrumOf ∅) := by sorry

end NicerEars.TSP
