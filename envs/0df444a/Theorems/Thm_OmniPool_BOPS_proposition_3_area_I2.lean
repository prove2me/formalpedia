-- Prove2me | Theorems.Thm_OmniPool_BOPS_proposition_3_area_I2
-- name    : OmniPool.BOPS.proposition_3_area_I2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:42.837446+00:00
-- url     : https://prove2.me/theorems/901374aa-7d9c-4f09-92fb-7697cd7fb6ab
-- title:
--   Proof of Proposition 3, Area (I-2), p. OA7 — max of (2) at (1,0) ≤ max of (4) at φ_s = 1
-- statement:
--   Under the standing assumptions (nonnegative, integrable market sizes of positive means, $0<c_b<p_b$, $0\le c_o\le c_b$, $k>0$, Assumption (U)), suppose $k\le t$. Let $q_s$ be the unique maximizer over $q\ge0$ of the BASE profit (2) with beliefs $(\hat\phi_s,\hat\phi_m)=(1,0)$ and $q_p$ the unique maximizer over $q\ge 0$ of the BOPS profit (4) with $\hat\phi_s=1$. Then
--   $$\Pi_B=\pi_B(q_s\mid 1,0)\ \le\ \pi_P(q_p\mid 1)=\Pi_P .$$
--
--   In Area (I-2) the BASE equilibrium is $(q_s,1,0)$ and the BOPS equilibrium is $(q_p,1)$, so this is the first case of the proof of Proposition 3: pooling the BOPS demand onto the store inventory cannot lower the retailer's optimal profit.
--
--   **Formalization Note.** The comparison is stated without the region of Area (I-2), which it does not need; this is stronger than the case of the proof. $\Pi_B$ and $\Pi_P$ are written as the profits (2) and (4) at their maximizers, not the simplified forms of the page. Market sizes are nonnegative instead of normal: with normal market sizes the step "Clearly, $\Pi_B\le\Pi_P$" fails.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), proof of Proposition 3, first case (Area (I-2)), p. OA7, "Clearly, Π_B ≤ Π_P"

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem proposition_3_area_I2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hkt : M.k ≤ M.t) :
    profitB M P Ds Dm 1 0 qs ≤ profitP M P Ds Dm 1 qp := by sorry

end OmniPool.BOPS
