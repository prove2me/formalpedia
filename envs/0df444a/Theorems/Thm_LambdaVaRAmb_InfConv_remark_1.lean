-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_remark_1
-- name    : LambdaVaRAmb.InfConv.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:54.116821+00:00
-- url     : https://prove2.me/theorems/3f017754-aca0-405d-966d-5d8dadb2e408
-- title:
--   Remark 1 — under a continuous capacity, ΛVaR^w(X) < ∞ if λ⁻ > 0 or if Λ ∈ ℋ_I
-- statement:
--   Let $w$ be a continuous capacity on $(\Omega,\mathcal F)$ and $\Lambda:\mathbb R\to(0,1)$. Suppose that either $\lambda^-=\inf_{x\in\mathbb R}\Lambda(x)>0$, or $\Lambda$ is increasing. Then for every random variable $X$,
--   $$
--   \Lambda\mathrm{VaR}^w(X)<\infty .
--   $$
--
--   This finiteness is what lets Theorem 3 (which assumes risk measures with values in $[-\infty,\infty)$) apply to $\Lambda\mathrm{VaR}$ in Proposition 8.
--
--   **Formalization Note** The remark also says that the assumption is "required" and that it "can be removed from Proposition 8" when all $\Lambda_i$ increase; these are commentary and are not posed. $\lambda^-$ is the real infimum of the range of $\Lambda$, which is the true infimum since the range is nonempty and bounded below by $0$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 17, Remark 1

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem remark_1 {Ω : Type*} [MeasurableSpace Ω] (w : Set Ω → ℝ) (hw : IsContinuousCapacity w)
    (Λ : ℝ → ℝ) (hΛ : (LambdaVaRAmb.Robust.InH Λ ∧ 0 < sInf (Set.range Λ)) ∨ LambdaVaRAmb.Robust.InHI Λ) :
    ∀ X : Ω → ℝ, Measurable X → LambdaVaRAmb.Robust.LVaR Λ w X < ⊤ := by sorry

end LambdaVaRAmb.InfConv
