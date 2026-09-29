-- Prove2me | Theorems.Thm_JechSetTheory_solovay_split
-- name    : JechSetTheory.solovay_split
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T02:31:06.890369+00:00
-- url     : https://prove2.me/theorems/cc679192-fcb1-408a-b6a3-37f5dd59680f
-- title:
--   Jech, Theorem 8.10 (Solovay) — every stationary set splits into $\kappa$ disjoint stationary sets
-- statement:
--   Let $\kappa$ be a regular uncountable cardinal.
--
--   **Theorem (Solovay; Jech 8.10).** Every stationary subset $A \subseteq \kappa$ is the disjoint union of $\kappa$ stationary subsets: there is a family $\langle S_i : i < \kappa\rangle$ of pairwise disjoint stationary sets with
--
--   $$A \;=\; \bigcup_{i<\kappa} S_i .$$
--
--   In particular the closed unbounded filter on $\kappa$ is not an ultrafilter, and the quotient of $\mathcal{P}(\kappa)$ by the nonstationary ideal is atomless. Disjoint stationary families produced this way are the raw material of many independence arguments (stationary-set colourings, $\square$-principles, forcing with stationary sets).
--
--   **Formalization Note** The splitting family is indexed by the type `Below k` of ordinals below $\kappa$, which has cardinality $\kappa$, so "$\kappa$ many pieces" is expressed by the index type rather than by a cardinality hypothesis; every piece is required to be stationary, so the union is genuinely a $\kappa$-fold decomposition and no piece is empty.
-- source:
--   Thomas Jech, Set Theory, The Third Millennium Edition, revised and expanded, Springer Monographs in Mathematics, Springer 2003, ISBN 3-540-44085-2, Chapter 8, p. 95, Theorem 8.10 (Solovay), using Lemma 8.8 (p. 94) and Lemma 8.9 (pp. 94-95)

import Mathlib
import Definitions.Def_JechStationary

open Cardinal Order Set JechSetTheory

namespace JechSetTheory

theorem solovay_split (k : Cardinal) (hk : k.IsRegular) (hk₀ : ℵ₀ < k)
    (A : Set (Below k)) (hA : IsStationary A) :
    ∃ S : Below k → Set (Below k),
      (∀ i, IsStationary (S i)) ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      A = ⋃ i, S i := by sorry

end JechSetTheory
