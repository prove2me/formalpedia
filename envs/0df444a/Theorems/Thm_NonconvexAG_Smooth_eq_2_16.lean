-- Prove2me | Theorems.Thm_NonconvexAG_Smooth_eq_2_16
-- name    : NonconvexAG.Smooth.eq_2_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:43:37.966018+00:00
-- url     : https://prove2.me/theorems/b9ef8196-81f7-435d-af14-19f38695fe8b
-- title:
--   (2.16) — Σ_{τ=1}^k α_τ/Γ_τ = 1/Γ_k
-- statement:
--   Let $\{\alpha_k\}$ satisfy $\alpha_1=1$ and $\alpha_k\in(0,1)$ for $k\ge2$, and let $\Gamma_k$ be as in (2.6). Then for every $k\ge1$,
--   $$\sum_{\tau=1}^k\frac{\alpha_\tau}{\Gamma_\tau}=\frac1{\Gamma_k}.$$
--
--   So the weights $\Gamma_k\alpha_\tau/\Gamma_\tau$, $\tau=1,\dots,k$, form a probability vector, which is what allows Jensen's inequality in (2.17).
--
--   **Formalization Note** The statement is the outer ends of the chain (2.16).
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 6, (2.16)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

namespace NonconvexAG.Smooth

/-- (2.16), p. 6 (outer ends of the chain). -/
theorem eq_2_16 (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) :
    ∀ k, 1 ≤ k → ∑ τ ∈ Finset.Icc 1 k, α τ / Gamma α τ = 1 / Gamma α k := by sorry

end NonconvexAG.Smooth
