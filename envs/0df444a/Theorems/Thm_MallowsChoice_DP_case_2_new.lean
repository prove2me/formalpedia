-- Prove2me | Theorems.Thm_MallowsChoice_DP_case_2_new
-- name    : MallowsChoice.DP.case_2_new
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:46.73407+00:00
-- url     : https://prove2.me/theorems/15749514-834c-4ab8-8f37-a53dae8c32e1
-- title:
--   §4.1 Case 2, p. 17 — newly inserted offered product
-- statement:
--   Let $n\ge1$, $\theta\ge0$, and let $S$ contain $a_1$. If $1\le m<n$ and the newly inserted product $a_{m+1}$ also belongs to $S$, then for $1\le s\le m+1$,
--
--   $$
--   \pi(m+1,s,m+1)=\alpha_{s,m+1}
--      \sum_{i=1}^{m}\sum_{\ell=s}^{n}\pi(i,\ell,m).
--   $$
--
--   This is the new-product transition used in Algorithm 2's recursion (4).
--
--   **Formalization Note** Algorithm 2's line 1 assumes $a_1\in S$; that condition is essential here because the inner sum otherwise omits rankings with no previously offered product. The upper limit remains $n$ as printed, although $\pi(i,\ell,m)=0$ for $\ell>m$.
-- source:
--   Désir, Goyal, Jagabathula & Segev, Mallows-Smoothed Distribution over Rankings Approach for Modeling Choice, SSRN 3172997 (manuscript OPRE-2018-04-176, version of 2019-09-25; Oper. Res. doi:10.1287/opre.2020.2085), §4.1, Case 2 (new product), p. 17

import Mathlib
import Definitions.Def_MallowsChoice_DP_Setting

namespace MallowsChoice.DP

open Finset

/-- §4.1, Case 2, p. 17: the newly inserted offered product is chosen. -/
theorem case_2_new (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 ≤ θ)
    (S : Finset (Fin n)) (h1 : (⟨0, hn⟩ : Fin n) ∈ S)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (hin : (⟨m, hmn⟩ : Fin n) ∈ S) :
    ∀ s : ℕ, 1 ≤ s → s ≤ m + 1 →
      piProb θ S (m + 1) s (m + 1) =
        alpha θ s (m + 1) *
          ∑ i ∈ Icc 1 m, ∑ ℓ ∈ Icc s n, piProb θ S i ℓ m := by sorry

end MallowsChoice.DP
