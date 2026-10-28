-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_combined_terms
-- name    : HetExponomial.ChoiceProb.combined_terms
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:47.719926+00:00
-- url     : https://prove2.me/theorems/bf90d45a-eefb-4473-92fa-3ae20715fc5f
-- title:
--   Proof of Theorem 1, pp. 43–44 — combining the negative term of each line of (16) with the positive term below gives −λ_i(Σ_{u_j=a_w} λ_j)/(L_{B(a_{w+1})} L_{B(a_w)})·exp[…]
-- statement:
--   In the HEC model with $n\ge 2$ and rates $\lambda_j>0$, let $a_1<\dots<a_l$ be the distinct ideal utilities, let $u_i=a_k$, and write $B(x)=\{j: u_j\ge x\}$. For every level $w$ with $1\le w<k$, the negative term of the line of (16) carrying $B(a_{w+1})$ and the positive term of the line below it, carrying $B(a_w)$, are integrals from the same lower limit $a_k-a_w$. Their sum is
--   $$
--   \lambda_i\Big\{\int_{a_k-a_w}^\infty e^{-\sum_{j\in B(a_w)}\lambda_j(u_j-u_i+z)}dz-\int_{a_k-a_w}^\infty e^{-\sum_{j\in B(a_{w+1})}\lambda_j(u_j-u_i+z)}dz\Big\}
--   =\frac{-\lambda_i\big(\sum_{\{j:\,u_j=a_w\}}\lambda_j\big)}{\big(\sum_{j\in B(a_{w+1})}\lambda_j\big)\big(\sum_{j\in B(a_w)}\lambda_j\big)}\cdot\exp\Big[-\sum_{j\in B(a_w)}\lambda_j(u_j-a_w)\Big].
--   $$
--
--   These are the terms displayed on p. 44 of the proof of Theorem 1. Summed over $w$, they become the negative part of the closed form (3).
--
--   **Formalization Note** Levels are indexed from $0$. The paper's range $1\le w<k$ becomes Lean's `w < k`, and $a_{w+1}$ is `level u w'` with `w'.val = w.val + 1`. Both tail integrals are integrable, because $i\in B(a_{w+1})\subseteq B(a_w)$ (as $a_{w+1}\le a_k=u_i$). This makes both denominators positive.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), pp. 43–44, proof of Theorem 1 (terms after (16), 1 ≤ w < k)

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem combined_terms {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) (k : Fin (levels u).card) (hk : level u k = u i)
    (w w' : Fin (levels u).card) (hw : w < k) (hw' : w'.val = w.val + 1) :
    lam i * (tailInt u lam i (level u w) (u i - level u w)
              - tailInt u lam i (level u w') (u i - level u w)) =
      -(lam i * ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam j) /
        ((∑ j ∈ betterThan u (level u w'), lam j) * (∑ j ∈ betterThan u (level u w), lam j)) *
        Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - level u w))) := by sorry

end HetExponomial.ChoiceProb
