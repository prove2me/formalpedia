-- Prove2me | Theorems.Thm_OmniPool_BOPS_lemma_2
-- name    : OmniPool.BOPS.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:42.692542+00:00
-- url     : https://prove2.me/theorems/8991f320-f3f8-40f6-af05-7c000f437e5f
-- title:
--   Lemma 2, p. 13 — q_sm ≥ q_p ≥ q_s and ζ_p ≥ ζ_s (nonnegative market sizes)
-- statement:
--   Consider the BASE and BOPS models with nonnegative, integrable market sizes $D_s, D_m$ of positive means, prices and costs with $0<c_b<p_b$ and $0\le c_o\le c_b$, a positive store visiting cost $k$, and Assumption (U) $u_o\ge\max(t,u_b)$. Suppose $k\le t$ (omni-customers prefer BOPS), and let $q_s$, $q_{sm}$ and $q_p$ be the unique maximizers over $q\ge 0$ of the BASE profit (2) with beliefs $(\hat\phi_s,\hat\phi_m)=(1,0)$, of (2) with beliefs $(1,1)$, and of the BOPS profit (4) with $\hat\phi_s=1$. Then
--   $$q_{sm}\ \ge\ q_p\ \ge\ q_s\qquad\text{and}\qquad \zeta_p\ \ge\ \zeta_s,$$
--   where $\zeta_s=\mathbb E[\min(D_s,q_s)]/\mathbb E[D_s]$ and $\zeta_p=\mathbb E[\min(D_s,q_p)]/\mathbb E[D_s]$.
--
--   BOPS lets the store serve both store-only and BOPS customers, which reduces its overstocking risk relative to serving store-only customers alone, so the retailer stocks more and store-only customers see a higher fill rate. This ordering is used in the proof of Proposition 3 to split its region into Areas (I-2) and (I-3).
--
--   **Formalization Note.** Only the first sentence of Lemma 2 is stated. The "Moreover" clause ($\zeta_{sm}$ can be greater or less than $\zeta_p$) is an existence-of-instances claim proved by a normal-model limit and is omitted. Market sizes are nonnegative and integrable with positive means instead of normal (the paper's normal model makes Proposition 3 false); the hypothesis $k\le t$ is the paper's "special case of $k\le t$" in which $q_p$ is defined. "The optimal order quantity" is read as the unique maximizer over $q\ge0$.
-- source:
--   Hu, Xu, Xue & Yang, Demand Pooling in Omnichannel Operations, accepted manuscript (SSRN 3214047; Manage. Sci. 68(2):883–894, 2022, doi:10.1287/mnsc.2021.3964), Lemma 2, p. 13 (proof p. OA4)

import Mathlib
import Definitions.Def_OmniPool_BOPS_Setting

open MeasureTheory

namespace OmniPool.BOPS

theorem lemma_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Ds Dm : Ω → ℝ)
    (hDsi : Integrable Ds P) (hDmi : Integrable Dm P) (hDs0 : ∀ ω, 0 ≤ Ds ω) (hDm0 : ∀ ω, 0 ≤ Dm ω)
    (hmus : 0 < ∫ ω, Ds ω ∂P) (hmum : 0 < ∫ ω, Dm ω ∂P)
    (M : Market) (hcb : 0 < M.cb) (hcbpb : M.cb < M.pb) (hco : 0 ≤ M.co) (hcocb : M.co ≤ M.cb)
    (hk : 0 < M.k) (hU : max M.t M.ub ≤ M.uo)
    (qs : ℝ) (hqs : IsUniqueMaxNonneg (profitB M P Ds Dm 1 0) qs)
    (qsm : ℝ) (hqsm : IsUniqueMaxNonneg (profitB M P Ds Dm 1 1) qsm)
    (qp : ℝ) (hqp : IsUniqueMaxNonneg (profitP M P Ds Dm 1) qp)
    (hkt : M.k ≤ M.t) :
    qp ≤ qsm ∧ qs ≤ qp ∧ zetaS P Ds Dm qs ≤ zetaP P Ds qp := by sorry

end OmniPool.BOPS
