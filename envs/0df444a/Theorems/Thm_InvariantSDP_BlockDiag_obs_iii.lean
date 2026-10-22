-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_obs_iii
-- name    : InvariantSDP.BlockDiag.obs_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:32.180977+00:00
-- url     : https://prove2.me/theorems/e882a8af-aa0b-4da4-a1cd-81fed654767c
-- title:
--   Proof of Theorem 2.7, p. 14, observation (iii) — each block $I_iXI_j$ is zero or a nonzero multiple of a square unitary
-- statement:
--   In the setting of observations (i)–(ii) — $\mathcal A \subseteq \mathbb C^{n\times n}$ a matrix ∗-algebra, $\mathcal B$ an inclusionwise maximal commutative ∗-subalgebra of $\mathcal A$ in diagonal form $\mathcal B = \mathbb C I_1 + \dots + \mathbb C I_k$ for a partition $[n] = S_0 \cup S_1 \cup \dots \cup S_k$ with $S_1,\dots,S_k$ nonempty — let $X \in \mathcal A$, let $i, j \in \{1, \dots, k\}$ and put $M = I_i X I_j$. Then either $M = 0$, or $|S_i| = |S_j|$ and there is a real $c > 0$ with
--   $$M M^* = c\, I_i \qquad\text{and}\qquad M^* M = c\, I_j .$$
--
--   This is the paper's statement that the block $X_{ij}$ is either zero or a nonzero multiple of a (square) unitary matrix: the latter means exactly that $X_{ij}$ is square and $X_{ij}X_{ij}^* = X_{ij}^*X_{ij} = c\,I$ with $c = |\text{multiple}|^2 > 0$. It drives the transitivity of the relation $\sim$ and the final identification of a simple matrix ∗-algebra with a full matrix algebra.
--
--   **Formalization Note** The block is the full-size product $I_iXI_j$; "nonzero multiple of a square unitary" is encoded as equal part sizes plus the two Gram identities with a common positive constant. The proof's "without loss of generality $|S_i| \ge |S_j|$" is not reproduced: the conclusion is symmetric. Blocks with $i = 0$ or $j = 0$ are omitted, as they vanish by (ii). Indices are 0-based.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 14, proof of Theorem 2.7, observation (iii)

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

open Matrix

/-- Proof of Theorem 2.7, p. 14, observation (iii): in the setting of observations (i)–(ii), every
off-diagonal block `M = I_i X I_j` is either zero or a nonzero multiple of a square unitary matrix, i.e.
`|S_i| = |S_j|` and `M Mᴴ = c I_i`, `Mᴴ M = c I_j` for some real `c > 0`. -/
theorem obs_iii {n k : ℕ} (A B : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (S : Fin n → Option (Fin k)) (hB : IsMaxCommutative A B) (hS : IsDiagForm B S)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X ∈ A) (i j : Fin k) :
    zeroOneDiag S (some i) * X * zeroOneDiag S (some j) = 0 ∨
      ((Finset.univ.filter fun l => S l = some i).card =
          (Finset.univ.filter fun l => S l = some j).card ∧
        ∃ c : ℝ, 0 < c ∧
          (zeroOneDiag S (some i) * X * zeroOneDiag S (some j)) *
              (zeroOneDiag S (some i) * X * zeroOneDiag S (some j))ᴴ =
            (c : ℂ) • zeroOneDiag S (some i) ∧
          (zeroOneDiag S (some i) * X * zeroOneDiag S (some j))ᴴ *
              (zeroOneDiag S (some i) * X * zeroOneDiag S (some j)) =
            (c : ℂ) • zeroOneDiag S (some j)) := by sorry

end InvariantSDP.BlockDiag
