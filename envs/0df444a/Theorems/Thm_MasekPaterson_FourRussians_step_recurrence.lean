-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_step_recurrence
-- name    : MasekPaterson.FourRussians.step_recurrence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:04:23.205312+00:00
-- url     : https://prove2.me/theorems/c4b47988-4c24-4c03-858f-08da3f374a6f
-- title:
--   Corollary 1 (of Theorem 2) — the recurrence in terms of steps
-- statement:
--   Let $\gamma$ be a nonnegative, normalized cost function and $A, B$ strings with edit matrix $\delta_{i,j}$. For all $i, j$ with $1 \le i \le |A|$ and $1 \le j \le |B|$, the vertical step $\delta_{i,j} - \delta_{i-1,j}$ and the horizontal step $\delta_{i,j} - \delta_{i,j-1}$ satisfy
--
--   $$\delta_{i,j} - \delta_{i-1,j} = \min\{R_{A_i,B_j} - (\delta_{i-1,j} - \delta_{i-1,j-1}),\ D_{A_i},\ I_{B_j} + (\delta_{i,j-1} - \delta_{i-1,j-1}) - (\delta_{i-1,j} - \delta_{i-1,j-1})\},$$
--
--   $$\delta_{i,j} - \delta_{i,j-1} = \min\{R_{A_i,B_j} - (\delta_{i,j-1} - \delta_{i-1,j-1}),\ D_{A_i} + (\delta_{i-1,j} - \delta_{i-1,j-1}) - (\delta_{i,j-1} - \delta_{i-1,j-1}),\ I_{B_j}\}.$$
--
--   The steps leaving a cell are determined by the steps entering it and the two characters $A_i, B_j$, without reference to the absolute values of $\delta$. Algorithm Y is exactly this recurrence.
--
--   **Formalization Note** The corollary prints no range for $i, j$; it inherits Theorem 2's range $1 \le i \le |A|$, $1 \le j \le |B|$ and its hypotheses (nonnegative, normalized $\gamma$).
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 21, Corollary 1 (of Theorem 2)

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Corollary 1 (of Theorem 2): the Wagner–Fischer recurrence in terms of steps. For
`1 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|` and a nonnegative normalized cost function,
`δ_{i,j} − δ_{i−1,j} = min{R_{A_i,B_j} − (δ_{i−1,j} − δ_{i−1,j−1}), D_{A_i},
  I_{B_j} + (δ_{i,j−1} − δ_{i−1,j−1}) − (δ_{i−1,j} − δ_{i−1,j−1})}` and
`δ_{i,j} − δ_{i,j−1} = min{R_{A_i,B_j} − (δ_{i,j−1} − δ_{i−1,j−1}),
  D_{A_i} + (δ_{i−1,j} − δ_{i−1,j−1}) − (δ_{i,j−1} − δ_{i−1,j−1}), I_{B_j}}`. -/
theorem step_recurrence {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    dmat γ A B i j - dmat γ A B (i - 1) j =
      min (min (replCost γ A[i - 1] B[j - 1]
                  - (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1)))
               (delCost γ A[i - 1]))
          (insCost γ B[j - 1] + (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1))
                  - (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1))) ∧
    dmat γ A B i j - dmat γ A B i (j - 1) =
      min (min (replCost γ A[i - 1] B[j - 1]
                  - (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1)))
               (delCost γ A[i - 1] + (dmat γ A B (i - 1) j - dmat γ A B (i - 1) (j - 1))
                  - (dmat γ A B i (j - 1) - dmat γ A B (i - 1) (j - 1))))
          (insCost γ B[j - 1]) := by sorry

end MasekPaterson.FourRussians
