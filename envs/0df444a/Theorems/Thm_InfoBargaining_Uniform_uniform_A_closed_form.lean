-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_uniform_A_closed_form
-- name    : InfoBargaining.Uniform.uniform_A_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:24.147908+00:00
-- url     : https://prove2.me/theorems/b576a3d9-1e6a-4fd3-b346-6ecd0aa67c10
-- title:
--   Display, p. 13 — under the uniform prior, A(α, c) = max{1/2 − c, 0} for α ≤ |1 − 2c| and [(1+α)/2 − c]²/(2α) for α ≥ |1 − 2c|
-- statement:
--   Let the prior be uniform on $[0,1]$ and let $A(\alpha,c)$ be the total ex ante surplus (7), the expectation of $\big(\alpha w+(1-\alpha)/2-c\big)^+$ for $w$ uniform on $[0,1]$. For every $\alpha\in(0,1)$ and every cost $c\in(0,1)$,
--   $$A(\alpha,c)=\begin{cases}\max\{1/2-c,\,0\}, & \alpha\le|1-2c|,\\[4pt] \dfrac{[(1+\alpha)/2-c]^2}{2\alpha}, & \alpha\ge|1-2c|.\end{cases}$$
--
--   The posterior mean is uniform on $[(1-\alpha)/2,(1+\alpha)/2]$; the first case is the one in which $c$ lies outside that interval, the second the one in which it lies inside. This closed form is what makes the corner-solution analysis of Corollary 1 explicit.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 13, display after “The total ex ante surplus in (7) can be reduced as”

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem uniform_A_closed_form (α c : ℝ) (hα : α ∈ Set.Ioo (0:ℝ) 1) (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    (α ≤ |1 - 2 * c| → A α c = max (1 / 2 - c) 0) ∧
    (|1 - 2 * c| ≤ α → A α c = ((1 + α) / 2 - c) ^ 2 / (2 * α)) := by sorry

end InfoBargaining.Uniform
