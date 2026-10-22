-- Prove2me | Theorems.Thm_OmniPool_BOPS_proposition_3_area_I3
-- name    : OmniPool.BOPS.proposition_3_area_I3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:48.226982+00:00
-- url     : https://prove2.me/theorems/ac2194ff-5d98-4922-894d-a7de60d5fbc8
-- title:
--   Proof of Proposition 3, Area (I-3), p. OA7 — (2) at (0,0) ≤ max of (4) at φ_s = 1
-- statement:
--   Under the standing assumptions (nonnegative, integrable market sizes of positive means, $0<c_b<p_b$, $0\le c_o\le c_b$, $k>0$, Assumption (U)), suppose $k\le t$, and let $q_p$ be the unique maximizer over $q\ge0$ of the BOPS profit (4) with $\hat\phi_s=1$. Then for every order quantity $q\ge 0$,
--   $$\pi_B(q\mid 0,0)\ \le\ \pi_P(q_p\mid 1),$$
--   where $\pi_B(q\mid 0,0)=-c_bq+(p_o-c_o)\mathbb E[D_m]$ is the BASE profit (2) when nobody shops offline.
--
--   In Area (I-3) the BASE equilibrium orders nothing and the retailer earns $\Pi_B=\max_{q\ge0}\pi_B(q\mid 0,0)=(p_o-c_o)\mathbb E[D_m]$, while BOPS earns $\Pi_P=\pi_P(q_p\mid 1)$; this is the second case of the proof of Proposition 3.
--
--   **Formalization Note.** The page writes $\Pi_B=\max_q\{(p_o-c_o)\mathbb E[D_m]\}$, dropping the $-c_bq$ term of (2) that vanishes at the optimum $q=0$; the statement keeps (2) and quantifies over all $q\ge0$. It is stated without the region of Area (I-3), which it does not need. Market sizes are nonnegative instead of normal (the paper's normal model makes Proposition 3 false).
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), proof of Proposition 3, second case (Area (I-3)), p. OA7, "Then, it directly follows that Π_B ≤ Π_P"

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem proposition_3_area_I3
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hkt : M.k ≤ M.t) :
    ∀ q : ℝ, 0 ≤ q → profitB M P Ds Dm 0 0 q ≤ profitP M P Ds Dm 1 qp := by sorry

end OmniPool.BOPS
