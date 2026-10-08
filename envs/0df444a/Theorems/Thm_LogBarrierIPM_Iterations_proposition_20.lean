-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_proposition_20
-- name    : LogBarrierIPM.Iterations.proposition_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:07:28.857802+00:00
-- url     : https://prove2.me/theorems/e453cfc7-6d91-4788-b8eb-603b4ba89a89
-- title:
--   Proposition 20 — the recursion for $x^\lambda$ gives the greatest point of $\{x\in\mathcal P':x_1\le\lambda\}$
-- statement:
--   Let $r\ge1$ and $\lambda\in\mathbb R$, and let $\mathcal P'\subseteq\mathbb T^{2r}$ be the tropical polyhedron defined by (26):
--   $$x_1\le2,\quad x_2\le1,\quad x_{2j+1}\le1+x_{2j-1},\quad x_{2j+1}\le1+x_{2j},\quad x_{2j+2}\le(1-1/2^j)+\max(x_{2j-1},x_{2j})\quad(1\le j<r).$$
--   Then the point $x^\lambda$ defined by the recursion
--   $$x^\lambda_1=\min(\lambda,2),\quad x^\lambda_2=1,\quad x^\lambda_{2j+1}=1+\min(x^\lambda_{2j-1},x^\lambda_{2j}),\quad x^\lambda_{2j+2}=(1-1/2^j)+\max(x^\lambda_{2j-1},x^\lambda_{2j})\quad(1\le j<r)$$
--   is the greatest element, for the coordinatewise order, of the tropical polyhedron
--   $$\{x\in\mathcal P':\ x_1\le\lambda\}.$$
--   That is, $x^\lambda$ belongs to this set and every point of the set is $\le x^\lambda$; it is the tropical barycenter of the set.
--
--   In the paper the tropical central path of $\mathrm{LW}_r$ at parameter $\lambda$ has $x$-part equal to this barycenter, so the recursion describes the tropical central path explicitly; its oscillating last two coordinates are what force many segments.
--
--   **Formalization Note** The page states Proposition 20 as "the point $x^\lambda$ [the $x$-part of the tropical central path] is given by the recursion". This item states what the proof on p. 19 establishes: the recursion yields the barycenter of $\{x\in\mathcal P':x_1\le\lambda\}$. The identification of $\mathcal P'$ with the valuation of the projected Puiseux feasible set, from (25)–(26) and [AGS16, Cor. 14], is the step that connects it with the tropical central path; it requires the Puiseux field and is not part of this item. $\mathbb T$ is `WithBot ℝ`.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 19, Proposition 20 and its proof, eqs. (26)–(27)

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_TropicalLW

namespace LogBarrierIPM.Iterations

/-- Proposition 20 (p. 19), in the form its proof establishes. For `r ≥ 1` and `λ ∈ ℝ`, the point
`x^λ` given by the recursion `x^λ_1 = min(λ, 2)`, `x^λ_2 = 1`,
`x^λ_{2j+1} = 1 + min(x^λ_{2j−1}, x^λ_{2j})`, `x^λ_{2j+2} = (1 − 1/2^j) + max(x^λ_{2j−1}, x^λ_{2j})`
(`1 ≤ j < r`) is the greatest element (the tropical barycenter) of
`{x ∈ 𝒫' : x_1 ≤ λ}`, where `𝒫' ⊆ 𝕋^{2r}` is the tropical polyhedron (26). -/
theorem proposition_20 (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) :
    IsGreatest {x | x ∈ tropicalLWSet r ∧ coord x 1 ≤ (lam : WithBot ℝ)}
      (fun k => ((xLam r lam k : ℝ) : WithBot ℝ)) := by sorry

end LogBarrierIPM.Iterations
