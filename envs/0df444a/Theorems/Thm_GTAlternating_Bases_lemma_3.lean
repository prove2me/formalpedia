-- Prove2me | Theorems.Thm_GTAlternating_Bases_lemma_3
-- name    : GTAlternating.Bases.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:09.417618+00:00
-- url     : https://prove2.me/theorems/03864a61-65d2-4b58-881b-b49d7708a49f
-- title:
--   Lemma 3, p. 9 — for self-conjugate µ ∈ λ↓, the embedding (4) is A_{n−1}-equivariant and maps V_µ^± into V_λ^±
-- statement:
--   Let $\lambda$ and $\mu$ be self-conjugate partitions with $\mu \in \lambda^{\downarrow}$, $|\mu| = n-1$, and let $\iota : V_\mu \to V_\lambda$ be the embedding (4), $v_T \mapsto v_{T^\lambda}$. Then
--
--   1. $\iota$ is $A_{n-1}$-equivariant;
--   2. $\iota(V_\mu^{+}) \subseteq V_\lambda^{+}$ and $\iota(V_\mu^{-}) \subseteq V_\lambda^{-}$.
--
--   In the paper's words, the restriction of $V_\lambda^{+}$ to $A_{n-1}$ contains $V_\mu^{+}$, and the restriction of $V_\lambda^{-}$ to $A_{n-1}$ contains $V_\mu^{-}$. This sign compatibility is what the normalisation (9) was chosen for.
--
--   **Formalization Note.** Clause 1 is the property of (4) stated on p. 6 ("an embedding of $V_\mu$ into the restriction of $V_\lambda$"), restricted to $A_{n-1}$; together with clause 2 it makes "contains" precise for the paper's identification of $V_\mu$ with a subspace of $V_\lambda$ via (4). $A_{n-1}$-equivariance is commutation with the generators $s_is_j$, $i, j \le n-2$.
-- source:
--   Geetha, Prasad, Comparison of Gelfand-Tsetlin bases for alternating and symmetric groups, arXiv:1606.04424v2, p. 9, Lemma 3 (with its proof, p. 10, and (4), p. 6)

import Mathlib
import Definitions.Def_GTAlternating_Bases_Model

namespace GTAlternating.Bases

open QAlgorithms.Papers.Independent.Renew46.P26

theorem lemma_3 (mu lam : YoungDiagram) (hmu : mu.transpose = mu) (hlam : lam.transpose = lam)
    (hedge : YoungEdge mu lam) :
    IsAltEquivariant mu.cells.card (embed mu lam) ∧
      ∀ s : Bool, (Vpm mu s).map (embed mu lam) ≤ Vpm lam s := by sorry

end GTAlternating.Bases
