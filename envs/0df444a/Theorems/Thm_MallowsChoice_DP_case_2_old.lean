-- Prove2me | Theorems.Thm_MallowsChoice_DP_case_2_old
-- name    : MallowsChoice.DP.case_2_old
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:41.055976+00:00
-- url     : https://prove2.me/theorems/2e8346bb-20e8-44e8-b1cd-adb590b3fc6a
-- title:
--   §4.1 Case 2, p. 17 — previously inserted products
-- statement:
--   Let $1\le m<n$ and suppose the newly inserted product $a_{m+1}$ belongs to the offer set $S$. For each earlier product $a_i$, $1\le i\le m$, and position $1\le s\le m+1$,
--
--   $$
--   \pi(i,s,m+1)=(1-\gamma_{s,m+1})\pi(i,s,m).
--   $$
--
--   This is the earlier-product part of Algorithm 2's transition when the new product is offered.
--
--   **Formalization Note** The formula also gives zero for an earlier product that is not in $S$, since its $\pi$ values are zero by definition.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), §4.1, Case 2 (old products), p. 17

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

namespace MallowsChoice.DP

/-- §4.1, Case 2, p. 17: an old product survives if the new one is inserted below it. -/
theorem case_2_old (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (S : Finset (Fin n))
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hin : (⟨m, hmn⟩ : Fin n) ∈ S) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m → ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
      piProb θ S i s (m + 1) =
        (1 - gamma θ s (m + 1)) * piProb θ S i s m := by sorry

end MallowsChoice.DP
