-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_blockY_final_steps
-- name    : MasekPaterson.FourRussians.blockY_final_steps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:05:03.331042+00:00
-- url     : https://prove2.me/theorems/d59078ba-06a4-4045-876d-439283ab9b71
-- title:
--   Algorithm Y returns the final step vectors of every $m \times m$ submatrix
-- statement:
--   Let $\gamma$ be a nonnegative, normalized cost function and $A, B$ strings with edit matrix $\delta_{i,j}$. Consider the $(i, j, m)$ submatrix, whose upper-left entry is $\delta_{i,j}$, with $i + m \le |A|$ and $j + m \le |B|$. Run Algorithm Y on the strings $C = A^{i+1, i+m}$ and $D = B^{j+1, j+m}$ and the submatrix's actual initial step vectors
--
--   $$R = \langle \delta_{i+k,j} - \delta_{i+k-1,j} \rangle_{k=1}^{m} \ \text{(left column)}, \qquad S = \langle \delta_{i,j+k} - \delta_{i,j+k-1} \rangle_{k=1}^{m} \ \text{(top row)}.$$
--
--   Then its output $(R', S')$ is the submatrix's actual pair of final step vectors:
--
--   $$R' = \langle \delta_{i+k,j+m} - \delta_{i+k-1,j+m} \rangle_{k=1}^{m} \ \text{(right column)}, \qquad S' = \langle \delta_{i+m,j+k} - \delta_{i+m,j+k-1} \rangle_{k=1}^{m} \ \text{(bottom row)}.$$
--
--   This is the statement, made in Section 2.1, that each submatrix is determined by its two initial step vectors and its two strings, and that Algorithm Y computes its final step vectors; Algorithm Z relies on it for every block.
--
--   **Formalization Note** The paper states this in prose ("each $(i, j, k)$ submatrix may be determined by a starting value $\delta(i,j)$, two initial step vectors … along with the two strings", and "Algorithm Y calculates a submatrix of steps according to Corollary 1"); it is not a numbered result. Vectors are 0-based in Lean: entry `k : Fin m` is the paper's entry $k+1$. For $m = 0$ the statement is trivially true.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 22, Section 2.1 (paragraph before Algorithm Y, and Algorithm Y)

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_FourRussians_algorithms
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Algorithm Y computes a submatrix's final step vectors (§2.1): for the `(i, j, m)`
submatrix of the edit matrix of `A, B` (upper-left entry `δ_{i,j}`, with `i + m ≤ |A|`,
`j + m ≤ |B|`), Algorithm Y applied to the strings `C = A^{i+1,i+m}`, `D = B^{j+1,j+m}` and
the actual initial step vectors `R = ⟨δ_{i+k,j} − δ_{i+k−1,j}⟩_{k=1..m}` (left column) and
`S = ⟨δ_{i,j+k} − δ_{i,j+k−1}⟩_{k=1..m}` (top row) returns the actual final step vectors
`R' = ⟨δ_{i+k,j+m} − δ_{i+k−1,j+m}⟩_{k=1..m}` (right column) and
`S' = ⟨δ_{i+m,j+k} − δ_{i+m,j+k−1}⟩_{k=1..m}` (bottom row). Vectors are 0-based in Lean:
entry `k : Fin m` is the paper's entry `k + 1`. -/
theorem blockY_final_steps {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j m : ℕ)
    (hiA : i + m ≤ A.length) (hjB : j + m ≤ B.length) :
    blockY γ m
        (fun k => A[i + k.val]) (fun k => B[j + k.val])
        (fun k => dmat γ A B (i + k.val + 1) j - dmat γ A B (i + k.val) j)
        (fun k => dmat γ A B i (j + k.val + 1) - dmat γ A B i (j + k.val)) =
      (fun k => dmat γ A B (i + k.val + 1) (j + m) - dmat γ A B (i + k.val) (j + m),
       fun k => dmat γ A B (i + m) (j + k.val + 1) - dmat γ A B (i + m) (j + k.val)) := by sorry

end MasekPaterson.FourRussians
