-- Prove2me | Theorems.Thm_OmniPool_BOPS_proposition_1_iii
-- name    : OmniPool.BOPS.proposition_1_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:37.401989+00:00
-- url     : https://prove2.me/theorems/5c0d0f64-c863-46c3-ba67-8bb487cf95d5
-- title:
--   Proposition 1(iii), p. 11 — if k > max(ζ_s u_b, ζ_sm u_b − (u_o − t)), the BASE equilibrium is q^B = 0, (φ_s, φ_m) = (0,0)
-- statement:
--   In the BASE model with nonnegative, integrable market sizes of positive means, $0<c_b<p_b$, $0\le c_o\le c_b$, $k>0$ and Assumption (U) $u_o\ge\max(t,u_b)$, let $q_s$, $q_{sm}$ be the unique maximizers over $q\ge0$ of the profit (2) under beliefs $(1,0)$ and $(1,1)$, with fill rates $\zeta_s$ and $\zeta_{sm}$. If
--   $$k\ >\ \max\big(\zeta_su_b,\ \zeta_{sm}u_b-(u_o-t)\big),$$
--   then a Pareto-dominant RE equilibrium of BASE exists, and every Pareto-dominant RE equilibrium has $q^B=0$ and $(\phi^B_s,\phi^B_m)=(0,0)$: nobody visits the store, store-only customers exit and omni-customers buy online.
--
--   This is the BASE benchmark of Area (I-3) in the proof of Proposition 3.
--
--   **Formalization Note.** Market sizes are nonnegative and integrable with positive means instead of normal (the paper's normal model makes Proposition 3 false). No Lemma 1 hypothesis is needed for this part. The final sentence of Proposition 1 is the online-demand term of (2), not a separate conclusion. Equilibria are the fixed points of Definition A1; Pareto dominance compares the retailer, store-only customers and omni-customers.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), Proposition 1(iii), p. 11 (proof pp. OA1–OA4, Case 3)

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem proposition_1_iii
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qsm : ℝ) (hqsm : IsUniqueMaxNonneg (profitB M P Ds Dm 1 1) qsm)
    (hreg : max (zetaS P Ds Dm qs * M.ub) (zetaSM P Ds Dm qsm * M.ub - (M.uo - M.t)) < M.k) :
    (∃ e, IsParetoREE_B M P Ds Dm e) ∧
      ∀ e, IsParetoREE_B M P Ds Dm e → e.q = 0 ∧ e.φs = 0 ∧ e.φm = 0 := by sorry

end OmniPool.BOPS
