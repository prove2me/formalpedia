-- Prove2me | Theorems.Thm_OmniPool_BOPS_proposition_3
-- name    : OmniPool.BOPS.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:44.675033+00:00
-- url     : https://prove2.me/theorems/c527fec8-683d-4471-92c3-678dc745d220
-- title:
--   Proposition 3, p. 16 — if ζ_sm u_b − u_o + t < k ≤ min(t, ζ_p u_b), BOPS benefits the retailer (nonnegative market sizes)
-- statement:
--   **Demand pooling effect.** A retailer sells through a brick-and-mortar store and an online channel. Store-only customers (market size $D_s$) buy only in the store; omni-customers (market size $D_m$) can buy online, in the store, or, when the retailer offers buy-online-pickup-at-store (BOPS), reserve online and collect in the store. Market sizes are nonnegative, integrable and have positive means. Prices and costs satisfy $0<c_b<p_b$ and $0\le c_o\le c_b$, the store visiting cost is $k>0$, the online waiting cost is $t$, and Assumption (U) $u_o\ge\max(t,u_b)$ holds.
--
--   Let $q_s$, $q_{sm}$ be the unique optimal store order quantities of the BASE model (independent channels) when only store-only customers, respectively both segments, shop offline, and $q_p$ the unique optimal order quantity of the BOPS model when store-only customers shop offline; let $\zeta_{sm}=\mathbb E[\min(D_m+D_s,q_{sm})]/\mathbb E[D_m+D_s]$ and $\zeta_p=\mathbb E[\min(D_s,q_p)]/\mathbb E[D_s]$ be the corresponding fill rates. If
--   $$\zeta_{sm}u_b-u_o+t\ <\ k\ \le\ \min(t,\ \zeta_pu_b),$$
--   then a Pareto-dominant rational-expectations equilibrium exists under BASE and under BOPS, and for every Pareto-dominant equilibrium of each,
--   $$\Pi_B\ \le\ \Pi_P,$$
--   where $\Pi_B$ and $\Pi_P$ are the retailer's expected profits at those equilibria: BOPS benefits the retailer.
--
--   When the online waiting cost is relatively low and the store visiting cost lower still (Areas I-2 and I-3 of Figure 3 of the paper), introducing BOPS moves omni-customers from the online channel to the store inventory, which the retailer then pools with store-only demand.
--
--   **Formalization Note.** This is a corrected statement. The paper assumes normal market sizes, and in that model the proposition is false: negative demand mass makes the expected BOPS sales term negative, and the step "Clearly, $\Pi_B\le\Pi_P$" of the proof fails (a counterexample is recorded with the mission). Here market sizes are arbitrary nonnegative integrable random variables with positive means; Assumption (M), the correlation and the equal coefficients of variation are not used. Equilibria are the fixed points of Definitions A1/A2 (the retailer's decision is an optimal order quantity over $q\ge0$ given the beliefs); "the RE equilibrium" of the paper is the Pareto-dominant one; BASE Pareto dominance compares retailer, store-only and omni-customers, BOPS Pareto dominance the retailer and store-only customers. "Benefits" is the weak inequality of the proof. The existence conjuncts rule out a vacuous comparison.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), Proposition 3, p. 16 (proof p. OA7)

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem proposition_3
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qsm : ℝ) (hqsm : IsUniqueMaxNonneg (profitB M P Ds Dm 1 1) qsm)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hlo : zetaSM P Ds Dm qsm * M.ub - M.uo + M.t < M.k)
    (hhi : M.k ≤ min M.t (zetaP P Ds qp * M.ub)) :
    (∃ e, IsParetoREE_B M P Ds Dm e) ∧ (∃ e, IsParetoREE_P M P Ds Dm e) ∧
      ∀ eB eP, IsParetoREE_B M P Ds Dm eB → IsParetoREE_P M P Ds Dm eP →
        retailerB M P Ds Dm eB ≤ retailerP M P Ds Dm eP := by sorry

end OmniPool.BOPS
