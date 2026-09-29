-- Prove2me | Theorems.Thm_MasekPaterson_FourRussians_initial_vectors
-- name    : MasekPaterson.FourRussians.initial_vectors
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T23:03:17.955127+00:00
-- url     : https://prove2.me/theorems/419c5100-8d1a-4a02-933f-9e7451f267b7
-- title:
--   Theorem 1 [7] — the first row and column of the edit matrix
-- statement:
--   Let $\gamma$ be a nonnegative, normalized cost function (that is, $\gamma(a \to b) = \delta(\gamma, a, b)$ for every edit operation), and let $A, B$ be strings with edit matrix $\delta_{i,j} = \delta(\gamma, A^i, B^j)$. Then $\delta_{0,0} = 0$, and
--
--   $$\delta_{i,0} = \sum_{1 \le r \le i} D_{A_r} \quad (1 \le i \le |A|), \qquad \delta_{0,j} = \sum_{1 \le r \le j} I_{B_r} \quad (1 \le j \le |B|).$$
--
--   This gives the initial vectors (first row and column) of the edit matrix, from which the Wagner–Fischer recurrence (Theorem 2) computes the rest. The paper cites it from Wagner and Fischer [7].
--
--   **Formalization Note** The paper states both formulas under the joint condition "$1 \le i \le |A|, 1 \le j \le |B|$"; each formula involves only one of the two indices, so each is stated with its own range, which is the same content and does not become vacuous when the other string is empty. The paper's standing assumption $|A| \ge |B|$ (used only for running times) is dropped. $\sum_{1 \le r \le i} D_{A_r}$ is written as the sum of $D$ over the first $i$ characters of $A$.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 20, Theorem 1 [7]

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Theorem 1 [Wagner–Fischer]: `δ_{0,0} = 0`, `δ_{i,0} = ∑_{1≤r≤i} D_{A_r}` for
`1 ≤ i ≤ |A|`, and `δ_{0,j} = ∑_{1≤r≤j} I_{B_r}` for `1 ≤ j ≤ |B|`, for a nonnegative
normalized cost function. -/
theorem initial_vectors {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hN : IsNormalized γ) (A B : List α) :
    dmat γ A B 0 0 = 0 ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ A.length → dmat γ A B i 0 = ((A.take i).map (delCost γ)).sum) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ B.length → dmat γ A B 0 j = ((B.take j).map (insCost γ)).sum) := by sorry

end MasekPaterson.FourRussians
