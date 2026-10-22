-- Prove2me | Theorems.Thm_OmniPool_BOPS_proposition_2_i
-- name    : OmniPool.BOPS.proposition_2_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:41.848987+00:00
-- url     : https://prove2.me/theorems/1133ca00-8b34-4220-a757-7bde227b6057
-- title:
--   Proposition 2(i), p. 14 — if k ≤ min(t, ζ_p u_b), the BOPS equilibrium is q^P = q_p, φ^P_s = 1, omni-customers choose BOPS
-- statement:
--   In the BOPS model with nonnegative, integrable market sizes of positive means, $0<c_b<p_b$, $0\le c_o\le c_b$, $k>0$ and Assumption (U) $u_o\ge\max(t,u_b)$, let $q_p$ be the unique maximizer over $q\ge 0$ of the BOPS profit (4) with $\hat\phi_s=1$, and $\zeta_p=\mathbb E[\min(D_s,q_p)]/\mathbb E[D_s]$. If
--   $$k\ \le\ \min(t,\ \zeta_pu_b),$$
--   then omni-customers choose BOPS ($\mathbf 1_{\{k\le t\}}=1$), a Pareto-dominant RE equilibrium of BOPS exists, and every Pareto-dominant RE equilibrium has $q^P=q_p$ and $\phi^P_s=1$.
--
--   In the BOPS model omni-customers who face a stockout spill over to the online channel; this spill-over is part of the profit (4). The proposition is the BOPS side of both areas in the proof of Proposition 3.
--
--   **Formalization Note.** Market sizes are nonnegative and integrable with positive means instead of normal (the paper's normal model makes Proposition 3 false). Equilibria are the fixed points of Definition A2 with the retailer's decision an optimal order quantity; because the paper defines no BOPS payoff for omni-customers (their channel is fixed by $k$ versus $t$), Pareto dominance compares the retailer and the store-only customers.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), Proposition 2(i), p. 14 (proof pp. OA5–OA7, Case 1)

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem proposition_2_i
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hreg : M.k ≤ min M.t (zetaP P Ds qp * M.ub)) :
    bopsInd M = 1 ∧ (∃ e, IsParetoREE_P M P Ds Dm e) ∧
      ∀ e, IsParetoREE_P M P Ds Dm e → e.q = qp ∧ e.φs = 1 := by sorry

end OmniPool.BOPS
