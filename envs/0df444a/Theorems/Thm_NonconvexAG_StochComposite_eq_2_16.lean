-- Prove2me | Theorems.Thm_NonconvexAG_StochComposite_eq_2_16
-- name    : NonconvexAG.StochComposite.eq_2_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:24:05.023559+00:00
-- url     : https://prove2.me/theorems/3f332d86-c8a9-44c7-9dc2-31744a3999ad
-- title:
--   (2.16) — Σ_{τ=1}^k α_τ/Γ_τ = 1/Γ_k
-- statement:
--   Let $\alpha_1=1$, $\alpha_k\in(0,1)$ for $k\ge2$, and $\Gamma_k$ as in (2.6). Then for every $k\ge1$
--   $$\sum_{\tau=1}^k\frac{\alpha_\tau}{\Gamma_\tau}=\frac1{\Gamma_k}.$$
--
--   In the proof of Theorem 4 this identity collects the $L_f$-terms of the summed inequality into $\frac{L_f}{\Gamma_N}(\|x^*\|^2+2M^2)$.
--
--   **Formalization Note** Restated from mission 1 of this series because drafts cannot import one another.
-- source:
--   Ghadimi & Lan, Accelerated Gradient Methods for Nonconvex Nonlinear and Stochastic Programming, arXiv:1310.3787v1, p. 6, (2.16)

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Definitions.Def_NonconvexAG_StochComposite_RSAG
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace NonconvexAG.StochComposite

open GhadimiLan.RSG (E)
open ConvexOptAlg.SmoothGD

/-- (2.16), p. 6 (outer ends of the chain): `Σ_{τ=1}^k α_τ/Γ_τ = 1/Γ_k` for every `k ≥ 1`. -/
theorem eq_2_16 (α : ℕ → ℝ) (hα1 : α 1 = 1) (hα : ∀ k, 2 ≤ k → 0 < α k ∧ α k < 1) :
    ∀ k, 1 ≤ k → ∑ τ ∈ Finset.Icc 1 k, α τ / NonconvexAG.Smooth.Gamma α τ = 1 / NonconvexAG.Smooth.Gamma α k := by sorry

end NonconvexAG.StochComposite
