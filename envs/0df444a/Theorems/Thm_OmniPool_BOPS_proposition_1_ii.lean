-- Prove2me | Theorems.Thm_OmniPool_BOPS_proposition_1_ii
-- name    : OmniPool.BOPS.proposition_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:51.626688+00:00
-- url     : https://prove2.me/theorems/b7d69e3e-3588-4b67-a7c3-7b64a7bff805
-- title:
--   Proposition 1(ii), p. 11 — if ζ_sm u_b − (u_o − t) < k ≤ ζ_s u_b, the BASE equilibrium is q^B = q_s, (φ_s, φ_m) = (1,0)
-- statement:
--   In the BASE model (independent channels) with nonnegative, integrable market sizes of positive means, $0<c_b<p_b$, $0\le c_o\le c_b$, $k>0$ and Assumption (U) $u_o\ge\max(t,u_b)$, let $q_s$ and $q_{sm}$ be the unique maximizers over $q\ge0$ of the profit (2) under scenario I, $(\hat\phi_s,\hat\phi_m)=(1,0)$, and scenario II, $(1,1)$, with fill rates $\zeta_s=\mathbb E[\min(D_s,q_s)]/\mathbb E[D_s]$ and $\zeta_{sm}=\mathbb E[\min(D_m+D_s,q_{sm})]/\mathbb E[D_m+D_s]$. Assume $\zeta_s\le\zeta_{sm}$ (the conclusion of the paper's Lemma 1). If
--   $$\zeta_{sm}u_b-(u_o-t)\ <\ k\ \le\ \zeta_su_b,$$
--   then a Pareto-dominant RE equilibrium of BASE exists, and every Pareto-dominant RE equilibrium has store order quantity $q^B=q_s$, store-only customers buying offline ($\phi^B_s=1$) and omni-customers buying online ($\phi^B_m=0$).
--
--   In this intermediate range of the visiting cost, omni-customers prefer the online channel while store-only customers still find the store worthwhile; this is the BASE benchmark of Area (I-2) in the proof of Proposition 3.
--
--   **Formalization Note.** Market sizes are nonnegative and integrable with positive means instead of normal (the paper's normal model makes Proposition 3 false). Lemma 1 ($\zeta_{sm}\ge\zeta_s$) holds in the normal model but not for general nonnegative demand, so its conclusion is a hypothesis; Proposition 1 is introduced "with Lemma 1". The proposition's final sentence ("a fraction $(1-\phi^B_m)$ of omni-customers purchase online") is the online-demand term of (2) and is not a separate conclusion. Equilibria are the fixed points of Definition A1 with the retailer's decision an optimal order quantity; Pareto dominance compares the retailer, store-only customers and omni-customers.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), Proposition 1(ii), p. 11 (proof pp. OA1–OA4, Case 2)

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem proposition_1_ii
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qsm : ℝ) (hqsm : IsUniqueMaxNonneg (profitB M P Ds Dm 1 1) qsm)
    (hL1 : zetaS P Ds Dm qs ≤ zetaSM P Ds Dm qsm)
    (hreg : zetaSM P Ds Dm qsm * M.ub - (M.uo - M.t) < M.k ∧ M.k ≤ zetaS P Ds Dm qs * M.ub) :
    (∃ e, IsParetoREE_B M P Ds Dm e) ∧
      ∀ e, IsParetoREE_B M P Ds Dm e → e.q = qs ∧ e.φs = 1 ∧ e.φm = 0 := by sorry

end OmniPool.BOPS
