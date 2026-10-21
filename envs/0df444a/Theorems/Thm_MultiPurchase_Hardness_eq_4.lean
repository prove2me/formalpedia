-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_eq_4
-- name    : MultiPurchase.Hardness.eq_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:55.046656+00:00
-- url     : https://prove2.me/theorems/f903fa8c-de62-4073-a9e2-fea584659c70
-- title:
--   Eq. (4), p. 17 — R₂(C) as a ratio of quadratic forms in x^C with θij and r̂ij
-- statement:
--   Consider a BundleMVL-2 instance with products $W=\{1,\dots,n\}$, revenues $r_i$, weights $V_{\{i\}}$, $V_{\{i,j\}}$ and no-purchase weight $v_0$. For $C\subseteq W$ let $x^C_i=1$ if $i\in C$ and $0$ otherwise, and set
--   $$\theta_{ij}=\begin{cases}V_{\{i,j\}}/2 & i\ne j\\ V_{\{i\}} & i=j\end{cases},\qquad \hat r_{ij}=\begin{cases}r_i+r_j & i\ne j\\ r_i & i=j.\end{cases}$$
--   Then the expected revenue of $C$ is
--   $$R_2(C)=\frac{\sum_{i\in W}\sum_{j\in W}\hat r_{ij}\theta_{ij}x^C_ix^C_j}{v_0+\sum_{i\in W}\sum_{j\in W}\theta_{ij}x^C_ix^C_j}.$$
--
--   This rewrites the revenue as a ratio of two quadratic forms in the indicator vector of $C$, the form used in the Compare-Step and in the hardness proof.
--
--   **Formalization Note** The identity is stated for every instance, without the well-formedness conditions: it is an algebraic identity between two expressions for the same numerator and denominator (Lean's division by zero gives both sides the same value).
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, p. 17 (PDF 17), eq. (4), second equality

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

/-- Eq. (4), p. 17, second form: with `x^C_i` the indicator of `C`, `θᵢᵢ = V{i}`,
`θᵢⱼ = V{i,j}/2` and `r̂ᵢᵢ = rᵢ`, `r̂ᵢⱼ = rᵢ + rⱼ` (`i ≠ j`),
`R₂(C) = ∑_{i∈W} ∑_{j∈W} r̂ᵢⱼ θᵢⱼ x^C_i x^C_j / (v0 + ∑_{i∈W} ∑_{j∈W} θᵢⱼ x^C_i x^C_j)`. -/
theorem eq_4 (I : Instance) (C : Finset (Fin I.n)) :
    I.R2 C = (∑ i, ∑ j, I.rhat i j * I.theta i j * xC C i * xC C j) /
      (I.v0 + ∑ i, ∑ j, I.theta i j * xC C i * xC C j) := by sorry

end MultiPurchase.Hardness
