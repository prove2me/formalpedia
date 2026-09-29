-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_wagner_fischer_recurrence
-- name    : MasekPaterson.FourRussians.wagner_fischer_recurrence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:03:48.717631+00:00
-- url     : https://prove2.me/theorems/ec626cfd-85d9-4646-ae30-adeaad1fefee
-- title:
--   Theorem 2 [7] — the Wagner–Fischer recurrence for $\delta_{i,j}$
-- statement:
--   Let $\gamma$ be a nonnegative, normalized cost function and $A, B$ strings with edit matrix $\delta_{i,j} = \delta(\gamma, A^i, B^j)$. For all $i, j$ with $1 \le i \le |A|$ and $1 \le j \le |B|$,
--
--   $$\delta_{i,j} = \min\bigl(\delta_{i-1,j-1} + R_{A_i,B_j},\ \delta_{i-1,j} + D_{A_i},\ \delta_{i,j-1} + I_{B_j}\bigr).$$
--
--   Each internal entry of the edit matrix is thus determined by its three neighbours above and to the left; this is Wagner and Fischer's matrix-filling algorithm [7], and it is the basis of every step of the Masek–Paterson algorithm.
--
--   **Formalization Note** $\delta$ is the minimum over all edit sequences (Section 1.1), not the recurrence, so this is a genuine theorem. Normalization is needed: with $R_{a,c} = 10$, $R_{a,b} = R_{b,c} = 1$ and all insertions and deletions costing $100$, $\delta(\gamma, a, c) = 2$ while the right-hand side is $10$. Characters are 1-based as in the paper ($A_i$ is `A[i-1]`).
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 20, Theorem 2 [7]

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Theorem 2 [Wagner–Fischer]: for `1 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|`,
`δ_{i,j} = min(δ_{i−1,j−1} + R_{A_i,B_j}, δ_{i−1,j} + D_{A_i}, δ_{i,j−1} + I_{B_j})`,
for a nonnegative normalized cost function. `A_i` (1-based) is `A[i-1]`. -/
theorem wagner_fischer_recurrence {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    dmat γ A B i j =
      min (min (dmat γ A B (i - 1) (j - 1) + replCost γ A[i - 1] B[j - 1])
               (dmat γ A B (i - 1) j + delCost γ A[i - 1]))
          (dmat γ A B i (j - 1) + insCost γ B[j - 1]) := by sorry

end MasekPaterson.FourRussians
