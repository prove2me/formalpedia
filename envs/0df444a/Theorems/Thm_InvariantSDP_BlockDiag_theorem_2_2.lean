-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_theorem_2_2
-- name    : InvariantSDP.BlockDiag.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:26.123103+00:00
-- url     : https://prove2.me/theorems/21864cbf-60fa-4467-942e-75b20fe22718
-- title:
--   Theorem 2.2, p. 11 — a commutative matrix ∗-algebra is unitarily similar to $\{\lambda_1I_1+\dots+\lambda_kI_k\}$
-- statement:
--   Let $\mathcal A \subseteq \mathbb C^{n\times n}$ be a commutative matrix ∗-algebra. Then there exist a unitary matrix $U$ and a partition $[n] = S_0 \cup S_1 \cup \dots \cup S_k$ with $S_1, \dots, S_k$ nonempty such that
--   $$U^* \mathcal A U = \{\lambda_1 I_1 + \dots + \lambda_k I_k : \lambda_1, \dots, \lambda_k \in \mathbb C\},$$
--   where $I_i$ is the zero-one diagonal matrix with ones in the positions from $S_i$ and zeros elsewhere.
--
--   This is the simultaneous unitary diagonalization of a commutative matrix ∗-algebra, written as an equality of sets. The part $S_0$ collects the coordinates on which every element of $\mathcal A$ vanishes after the change of basis; it is empty exactly when $\mathcal A$ contains the identity. In the proof of Theorem 2.7 it puts a maximal commutative ∗-subalgebra in diagonal form.
--
--   **Formalization Note** $U$ ranges over `Matrix.unitaryGroup (Fin n) ℂ` and $U^*\mathcal A U$ is the set $\{U^{\mathsf H} X U : X \in \mathcal A\}$. The partition is `S : Fin n → Option (Fin k)` with `none` for $S_0$ (possibly empty) and the nonemptiness of $S_1,\dots,S_k$ stated explicitly; $k = 0$ (the case $\mathcal A = \{0\}$) is allowed.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 11, Theorem 2.2

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

open Matrix

/-- Theorem 2.2, p. 11: a commutative matrix ∗-algebra is unitarily similar to
`{λ₁I₁ + ⋯ + λ_kI_k : λ_i ∈ ℂ}` for a partition `[n] = S₀ ∪ S₁ ∪ ⋯ ∪ S_k` with `S₁, …, S_k` nonempty. -/
theorem theorem_2_2 {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hA : IsCommutative A) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ (k : ℕ) (S : Fin n → Option (Fin k)),
      (∀ i : Fin k, ∃ j, S j = some i) ∧
      {Y | ∃ X ∈ A, Y = Uᴴ * X * U} =
        Set.range fun l : Fin k → ℂ => ∑ i, l i • zeroOneDiag S (some i) := by sorry

end InvariantSDP.BlockDiag
