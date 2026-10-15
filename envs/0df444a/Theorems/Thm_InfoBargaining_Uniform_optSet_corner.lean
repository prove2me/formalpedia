-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_optSet_corner
-- name    : InfoBargaining.Uniform.optSet_corner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:31.958231+00:00
-- url     : https://prove2.me/theorems/71e0a4b4-3b16-47d9-a9a3-0762810683b0
-- title:
--   Proof of Corollary 1, p. 30 — with linear cost the optimal information level is a corner, α* ∈ {α̲, ᾱ}
-- statement:
--   Under the uniform prior and the linear cost $k(\alpha)=\bar k(\alpha-\underline\alpha)/(\bar\alpha-\underline\alpha)$, let $\theta_b\in(0,1)$ and $c\in(0,1)$, and let $\alpha^*$ denote the set of maximisers of $U_b(\alpha)=\theta_bA(\alpha,c)-k(\alpha)$ over $[\underline\alpha,\bar\alpha]$. Then
--
--   1. one of the corners is optimal: $\underline\alpha\in\alpha^*$ or $\bar\alpha\in\alpha^*$;
--   2. if $U_b(\underline\alpha)\neq U_b(\bar\alpha)$, only corners are optimal: $\alpha^*\subseteq\{\underline\alpha,\bar\alpha\}$.
--
--   This reduces the buyer's information choice to a comparison of the two corners, $U_b(\bar\alpha)-U_b(\underline\alpha)=\theta_b[A(\bar\alpha,c)-A(\underline\alpha,c)]-\bar k$.
--
--   **Formalization Note** The page writes "$\alpha^*\in\{\underline\alpha,\bar\alpha\}$". Read literally for every maximiser, this fails in one case: at $c=1/2$, $A(\alpha,1/2)=\alpha/8$ is linear, so when $\theta_b(\bar\alpha-\underline\alpha)/8=\bar k$ every $\alpha\in[\underline\alpha,\bar\alpha]$ is optimal. The statement therefore reads the claim as "a corner is optimal, and only corners are optimal unless the two corners tie".
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 30, Appendix, proof of Corollary 1, first paragraph, last sentence

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem optSet_corner (M : Model) (θb c : ℝ) (hθb : θb ∈ Set.Ioo (0:ℝ) 1)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    (M.αlo ∈ M.optSet θb c ∨ M.αhi ∈ M.optSet θb c) ∧
    (M.Ub θb c M.αlo ≠ M.Ub θb c M.αhi → M.optSet θb c ⊆ {M.αlo, M.αhi}) := by sorry

end InfoBargaining.Uniform
