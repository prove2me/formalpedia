-- Prove2me | Theorems.Thm_MallowsChoice_DP_case_1
-- name    : MallowsChoice.DP.case_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:28.626996+00:00
-- url     : https://prove2.me/theorems/b78f3912-1ece-43ad-be70-efa5aaf69657
-- title:
--   §4.1 Case 1, p. 17 — inserting an unoffered product
-- statement:
--   Let $1\le m<n$ and let $a_{m+1}\notin S$. With $\theta\ge0$, the newly inserted product has zero probability of being chosen. For every earlier product $a_i$, $1\le i\le m$, and every position $1\le s\le m+1$,
--
--   $$
--   \pi(m+1,s,m+1)=0,\qquad
--   \pi(i,s,m+1)=(1-\gamma_{s,m+1})\pi(i,s,m)
--      +\gamma_{s-1,m+1}\pi(i,s-1,m).
--   $$
--
--   This is the unoffered-product transition used in Algorithm 2's recursion (3).
--
--   **Formalization Note** The first equality is stated for every natural-number position; values outside $1\le s\le m+1$ are zero by definition. In particular $\gamma_{0,m+1}=0$ and $\pi(i,0,m)=0$.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), §4.1, Case 1, p. 17

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

namespace MallowsChoice.DP

/-- §4.1, Case 1, p. 17: the next inserted product is outside the offer set. -/
theorem case_1 (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (S : Finset (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hout : (⟨m, hmn⟩ : Fin n) ∉ S) :
    (∀ s : ℕ, piProb θ S (m + 1) s (m + 1) = 0) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
        piProb θ S i s (m + 1) =
          (1 - gamma θ s (m + 1)) * piProb θ S i s m +
            gamma θ (s - 1) (m + 1) * piProb θ S i (s - 1) m := by sorry

end MallowsChoice.DP
