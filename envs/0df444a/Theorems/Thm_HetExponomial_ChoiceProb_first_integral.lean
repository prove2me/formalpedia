-- Prove2me | Theorems.Thm_HetExponomial_ChoiceProb_first_integral
-- name    : HetExponomial.ChoiceProb.first_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:47.176117+00:00
-- url     : https://prove2.me/theorems/65c16811-426c-412b-b4b9-f5da276279f5
-- title:
--   Proof of Theorem 1, p. 43 — the first integral of (16) is G_i: λ_i ∫_0^∞ exp[−Σ_{j∈B_i} λ_j (u_j − u_i + z)] dz = G_i
-- statement:
--   In the HEC model with $n\ge 2$ and rates $\lambda_j>0$, let $i\in N$, let $B_i=\{j: u_j\ge u_i\}$ and $L_i=\sum_{j\in B_i}\lambda_j$. Then
--   $$
--   \lambda_i\int_0^\infty \exp\Big[-\sum_{j\in B_i}\lambda_j\,(u_j-u_i+z)\Big]\,dz
--   =\frac{\lambda_i}{L_i}\exp\Big[-\sum_{j\in B_i}\lambda_j(u_j-u_i)\Big]=G_i(\mathbf u,\boldsymbol\lambda).
--   $$
--
--   This is the evaluation of the first integral of display (16) in the proof of Theorem 1, where $B(a_k)=B_i$ because $u_i=a_k$. It produces the leading term $G_i$ of the closed form (3).
--
--   **Formalization Note** The left side is `lam i * tailInt u lam i (u i) 0`, the tail integral over $(0,\infty)$ for the set $B(u_i)=B_i$.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 43, proof of Theorem 1 ("Evaluating the first integral in the first line of (16) results in G_i")

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem first_integral {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j)
    (i : Fin n) :
    lam i * tailInt u lam i (u i) 0 = G u lam i := by sorry

end HetExponomial.ChoiceProb
