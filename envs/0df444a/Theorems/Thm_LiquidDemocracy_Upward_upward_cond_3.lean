-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_upward_cond_3
-- name    : LiquidDemocracy.Upward.upward_cond_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:31.32051+00:00
-- url     : https://prove2.me/theorems/bd3ec2d3-1c0e-4a10-ba86-1f9a5c55bac7
-- title:
--   Appendix B.3, p. 42 — some continuous distribution makes the Upward Delegation Model satisfy (3)
-- statement:
--   Let $p\in(0,1)$. There are a continuous distribution $\mathcal D$ supported in $[0,1]$ and $\alpha>0$ such that, for the instance drawn from the Upward Delegation Model,
--
--   $$\mathbb P_{\mathcal D,M^U_p,n}\Big[\sum_{i=1}^n p_i+\alpha n\le n/2\le\sum_{i=1}^n\mathrm{weight}_i(G_n)\,p_i-\alpha n\Big]\ \longrightarrow\ 1\qquad(n\to\infty).$$
--
--   This is condition (3) of Lemma 1: the average competence lies below $1/2$ while the competence of the counted votes after delegation lies above $1/2$, which is what makes positive gain possible.
--
--   **Formalization Note** The statement is existential in $\mathcal D$ and $\alpha$, as on the page; the page's witness is a uniform distribution $\mathcal U[0,1-2\eta]$ for small $\eta>0$ with $\alpha=\eta/2$, which is not part of the statement.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 42, Appendix B.3, 'Upward Delegation satisfies (3)'

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

namespace LiquidDemocracy.Upward

open MeasureTheory Filter Topology

/-- Appendix B.3, p. 42: for `p ∈ (0,1)` there is a continuous `𝒟` and `α > 0` with
`ℙ_{𝒟,M^U_p,n}[∑_i p_i + αn ≤ n/2 ≤ ∑_i weight_i(G_n) p_i − αn] = 1 − o(1)`, i.e. (3). -/
theorem upward_cond_3 (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ D ∈ ContClass, ∃ α > (0 : ℝ), Tendsto (fun n => (instanceLaw D (upward p) n).real
      {ω | ∑ i, ω.1 i + α * n ≤ (n : ℝ) / 2 ∧
        (n : ℝ) / 2 ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - α * n}) atTop (𝓝 1) := by sorry

end LiquidDemocracy.Upward
