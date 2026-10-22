-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_maxComm_commutant_subset
-- name    : InvariantSDP.BlockDiag.maxComm_commutant_subset
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:21.937993+00:00
-- url     : https://prove2.me/theorems/5de68e3b-7f24-4c6b-bd6e-2b97d84f2967
-- title:
--   Proof of Theorem 2.7, p. 14 — a maximal commutative ∗-subalgebra contains every element of $\mathcal A$ commuting with it
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a matrix ∗-algebra and let $\mathcal B \subseteq \mathcal A$ be an inclusionwise maximal commutative ∗-subalgebra of $\mathcal A$. Then every $X \in \mathcal A$ that commutes with every element of $\mathcal B$ is itself an element of $\mathcal B$:
--   $$X \in \mathcal A,\quad XY = YX \ \text{ for all } Y \in \mathcal B \quad\Longrightarrow\quad X \in \mathcal B.$$
--
--   This is the first step of the paper's elementary proof of Theorem 2.7: the relative commutant of $\mathcal B$ in $\mathcal A$ is $\mathcal B$ itself, which later forces the diagonal blocks of every element of $\mathcal A$ to be scalar.
--
--   **Formalization Note** Matrix ∗-algebras are `NonUnitalStarSubalgebra`s (no unit assumed); maximality is among commutative `NonUnitalStarSubalgebra`s between $\mathcal B$ and $\mathcal A$.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 14, proof of Theorem 2.7, first paragraph

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- Proof of Theorem 2.7, p. 14: if `ℬ ⊆ 𝒜` is an inclusionwise maximal commutative ∗-subalgebra, then every
element of `𝒜` commuting with all of `ℬ` lies in `ℬ`. -/
theorem maxComm_commutant_subset {n : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hB : IsMaxCommutative A B) :
    ∀ X ∈ A, (∀ Y ∈ B, X * Y = Y * X) → X ∈ B := by sorry

end InvariantSDP.BlockDiag
