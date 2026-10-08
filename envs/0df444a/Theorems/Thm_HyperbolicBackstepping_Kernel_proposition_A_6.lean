-- Prove2me | Theorems.Thm_HyperbolicBackstepping_Kernel_proposition_A_6
-- name    : HyperbolicBackstepping.Kernel.proposition_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:10.837125+00:00
-- url     : https://prove2.me/theorems/b82b8b88-a53e-48f8-8f0a-66b3493af96d
-- title:
--   Proposition A.6, p. 22 — exponential bound on the increment series
-- statement:
--   Let $\varphi$ be the source vector (A.32) of the Goursat system and $\Phi$ the integral operator (A.31), and define the increments $\Delta F^0=\varphi$, $\Delta F^{n+1}=\Phi[\Delta F^n]$. Let $\bar\phi$, $\bar C$, $K_\epsilon$ be the constants of (A.35). Then for every component $i=1,\dots,4$ and every $(x,\xi)\in\mathcal T$, the series $\sum_{n\ge0}\Delta F^n_i(x,\xi)$ converges and
--   $$\Big|\sum_{n=0}^\infty\Delta F_i^n(x,\xi)\Big|\le\bar\phi\,e^{\bar CK_\epsilon x}.\qquad\text{(A.45)}$$
--
--   The sum of this series is the candidate solution (A.34) of the integral equations; the bound gives its existence and boundedness, and, applied to the difference of two solutions, its uniqueness.
--
--   **Formalization Note** Convergence (summability) is stated as a separate conclusion, so the bound is not satisfied by Lean's default value $0$ for a divergent series.
-- source:
--   Coron, Vazquez, Krstic and Bastin, Local Exponential H² Stabilization of a 2 × 2 Quasilinear Hyperbolic System Using Backstepping, arXiv:1208.6475v1, pp. 22–23, Proposition A.6 and (A.45)–(A.46)

import Mathlib
import Definitions.Def_HyperbolicBackstepping_Kernel_Goursat

namespace HyperbolicBackstepping.Kernel

/-- Proposition A.6, pp. 22–23: absolute bound on the series of increments. -/
theorem proposition_A_6 (D : GoursatData) :
    ∀ j : Fin 4, ∀ x ξ : ℝ, (x, ξ) ∈ Tri →
      Summable (fun n : ℕ => dF D n j x ξ) ∧
      |∑' n : ℕ, dF D n j x ξ| ≤ phiBar D * Real.exp (CbarTot D * Keps D * x) := by sorry

end HyperbolicBackstepping.Kernel
