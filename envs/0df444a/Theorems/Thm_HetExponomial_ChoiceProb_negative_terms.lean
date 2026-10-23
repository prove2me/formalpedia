-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_negative_terms
-- name    : HetExponomial.ChoiceProb.negative_terms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:53.621021+00:00
-- url     : https://prove2.me/theorems/5ba886e7-fe96-4722-8a98-d97adbd47a0a
-- title:
--   Proof of Theorem 1, p. 44 — the combined terms at level a_w equal −Σ_{k'∈W_i^−, u_{k'}=a_w} (λ_i/L_{k'}^+)·G_{k'}
-- statement:
--   In the HEC model with $n\ge 2$ and rates $\lambda_j>0$, let $a_1<\dots<a_l$ be the distinct ideal utilities, let $u_i=a_k$, and let $1\le w<k$. The combined term of level $a_w$ in the proof of Theorem 1 equals the part of the negative sum in (3) that comes from the strictly worse choices at level $a_w$:
--   $$
--   \frac{-\lambda_i\big(\sum_{\{j:\,u_j=a_w\}}\lambda_j\big)}{\big(\sum_{j\in B(a_{w+1})}\lambda_j\big)\big(\sum_{j\in B(a_w)}\lambda_j\big)}\cdot\exp\Big[-\sum_{j\in B(a_w)}\lambda_j(u_j-a_w)\Big]
--   =-\sum_{k'\in W_i^-:\ u_{k'}=a_w}\frac{\lambda_i}{L_{k'}^+}\,G_{k'}(\mathbf u,\boldsymbol\lambda).
--   $$
--   Here $W_i^-=\{j: u_j<u_i\}$, $L_{k'}^+=\sum_{j: u_j>u_{k'}}\lambda_j$, and $G_{k'}$ is the exponomial term (2).
--
--   This identification is the last sentence of the proof of Theorem 1: "These make up the negative terms in the statement of the theorem." Since $W_i^-$ is the disjoint union, over the levels $a_w<a_k$, of the choices at level $a_w$, summing over $w$ gives the full negative sum in (3).
--
--   **Formalization Note** Levels are indexed from $0$, with $a_{w+1}$ as `level u w'` and `w'.val = w.val + 1`. Each $k'$ in the sum lies strictly below $u_i$, so $i\in B_{k'}^+$ and $L_{k'}^+\ge\lambda_i>0$. The total function `Lplus`, which is $0$ at a choice of maximal ideal utility, therefore never takes its default value here.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 44, proof of Theorem 1 ("These make up the negative terms in the statement of the theorem")

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem negative_terms {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) (k : Fin (levels u).card) (hk : level u k = u i)
    (w w' : Fin (levels u).card) (hw : w < k) (hw' : w'.val = w.val + 1) :
    -(lam i * ∑ j ∈ Finset.univ.filter (fun j => u j = level u w), lam j) /
        ((∑ j ∈ betterThan u (level u w'), lam j) * (∑ j ∈ betterThan u (level u w), lam j)) *
        Real.exp (-(∑ j ∈ betterThan u (level u w), lam j * (u j - level u w))) =
      -∑ k' ∈ (strictlyWorse u i).filter (fun k' => u k' = level u w),
          lam i / Lplus u lam k' * G u lam k' := by sorry

end HetExponomial.ChoiceProb
