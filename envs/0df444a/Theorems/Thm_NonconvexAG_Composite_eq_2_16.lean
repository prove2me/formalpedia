-- Prove2me | Theorems.Thm_NonconvexAG_Composite_eq_2_16
-- name    : NonconvexAG.Composite.eq_2_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:35:16.122999+00:00
-- url     : https://prove2.me/theorems/48ccf07e-b7db-4ec6-8665-4d481e370a28
-- title:
--   (2.16) — Σ_{τ=1}^k α_τ/Γ_τ = 1/Γ_k
-- statement:
--   Let $\alpha_1=1$, $\alpha_k\in(0,1)$ for $k\ge2$, and let $\Gamma_k$ be given by (2.6). Then for every $k\ge1$
--   $$\sum_{\tau=1}^k\frac{\alpha_\tau}{\Gamma_\tau}=\frac1{\Gamma_k}.$$
--
--   The identity follows from $\alpha_\tau/\Gamma_\tau=1/\Gamma_\tau-1/\Gamma_{\tau-1}$ for $\tau\ge2$. In Theorem 2 it gives the last inequality of (2.53).
--
--   **Formalization Note** Only the outer ends of the printed chain are stated. Restated from mission 1 of this series.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 6, (2.16)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Composite_ProxMap
import Definitions.Def_NonconvexAG_Composite_AGRun

namespace NonconvexAG.Composite

open ConvexOptAlg.SmoothGD

/-- (2.16), p. 6 (outer ends of the chain). -/
theorem eq_2_16 (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) :
    ∀ k, 1 ≤ k → ∑ τ ∈ Finset.Icc 1 k, α τ / NonconvexAG.Smooth.Gamma α τ = 1 / NonconvexAG.Smooth.Gamma α k := by sorry
end NonconvexAG.Composite
