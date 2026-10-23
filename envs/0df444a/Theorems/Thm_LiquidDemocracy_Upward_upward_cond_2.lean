-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_upward_cond_2
-- name    : LiquidDemocracy.Upward.upward_cond_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:29.886337+00:00
-- url     : https://prove2.me/theorems/dcaaf0e8-6932-4512-9158-1bef137ffc4d
-- title:
--   Appendix B.3, pp. 40–41 — the Upward Delegation Model satisfies (2) for every continuous distribution
-- statement:
--   Let $p\in(0,1)$ and let $\mathcal D$ be a continuous distribution supported in $[0,1]$. Then there is $\alpha\in(0,1)$ such that, for the instance $(\vec p_n,G_n)$ drawn from the Upward Delegation Model $\mathbb P_{\mathcal D,M^U_p,n}$,
--
--   $$\mathbb P_{\mathcal D,M^U_p,n}\Big[\sum_{i=1}^n\mathrm{weight}_i(G_n)\,p_i-\sum_{i=1}^n p_i\ge2\alpha n\Big]\ \longrightarrow\ 1\qquad(n\to\infty).$$
--
--   So upward delegation raises the total competence of the counted votes by a linear amount with high probability: condition (2) of Lemma 1.
--
--   **Formalization Note** $\alpha$ depends on $\mathcal D$ (the page takes $\alpha$ from the masses of $\mathcal D$ below some $a$ and above some $b>a$). The page writes $\mathrm{dels}_i$ on p. 41 where condition (2) has $\mathrm{weight}_i$; the statement is condition (2).
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, pp. 40–41, Appendix B.3, 'Upward Delegation satisfies (2)'

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

namespace LiquidDemocracy.Upward

open MeasureTheory Filter Topology

/-- Appendix B.3, pp. 40–41: for `p ∈ (0,1)` and every continuous `𝒟` there is `α ∈ (0,1)` with
`ℙ_{𝒟,M^U_p,n}[∑_i weight_i(G_n) p_i − ∑_i p_i ≥ 2αn] = 1 − o(1)`, i.e. `M^U_p` satisfies (2). -/
theorem upward_cond_2 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (D : Measure ℝ) (hD : D ∈ ContClass) :
    ∃ α ∈ Set.Ioo (0 : ℝ) 1, Tendsto (fun n => (instanceLaw D (upward p) n).real
      {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i}) atTop (𝓝 1) := by sorry

end LiquidDemocracy.Upward
