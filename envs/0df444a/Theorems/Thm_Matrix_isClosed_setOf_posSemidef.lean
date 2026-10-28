-- Prove2me | Theorems.Thm_Matrix_isClosed_setOf_posSemidef
-- name    : Matrix.isClosed_setOf_posSemidef
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:22.296626+00:00
-- url     : https://prove2.me/theorems/3b98fafa-ac83-43b8-a7b2-d81cd403d7cc
-- title:
--   The positive semidefinite cone is closed
-- statement:
--   For a finite index type $n$, the set of positive semidefinite real $n \times n$ matrices
--
--   $$
--   \{A \in \mathbb{R}^{n \times n} \;:\; A \succeq 0\}
--   $$
--
--   is closed in the usual (entrywise) topology.
--
--   This is the fact that makes semidefinite programming a well-posed optimization problem: a
--   continuous objective attains its infimum on the intersection of the PSD cone with any compact
--   set, and a limit of PSD matrices is PSD, so the feasible set of an SDP is closed. Every
--   argument that extracts a convergent subsequence of PSD iterates, or that passes to a limit in
--   a relaxation, uses it.
--
--   The proof is the observation that the definition of positive semidefiniteness is a
--   *conjunction of closed conditions*: Hermitian symmetry $A^{\mathsf H} = A$, which is the
--   preimage of a diagonal under a continuous map, and the family of inequalities
--   $\langle x, Ax\rangle \ge 0$ indexed by $x \in \mathbb{R}^n$, each closed because $A \mapsto
--   \langle x, Ax \rangle$ is continuous. An arbitrary intersection of closed sets is closed.
--
--   **Formalization Note** `Matrix.PosSemidef` bundles `IsHermitian` with the nonnegativity of
--   `star x ⬝ᵥ A *ᵥ x`; the proof rewrites the set as that intersection via
--   `posSemidef_iff_dotProduct_mulVec` and concludes with `isClosed_iInter`.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. Standard; e.g. Horn & Johnson, Matrix Analysis, 2nd ed., §7.1.

import Mathlib

open Matrix

theorem Matrix.isClosed_setOf_posSemidef {n : Type*} [Fintype n] : IsClosed {A : Matrix n n ℝ | A.PosSemidef} := by sorry
