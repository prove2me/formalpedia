-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_two_stage_uncertainty_separable
-- name    : MultistageRUC.Equiv.two_stage_uncertainty_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:00.881158+00:00
-- url     : https://prove2.me/theorems/88ea72e3-8ec1-44b4-ab32-a7d5e8886798
-- title:
--   Theorem 1, proof (i), second equality, p. 11 — the uncertainty set (3) is separable over time
-- statement:
--   Let $\mathcal D=\prod_{t\in\mathcal T}\mathcal D^t$ be the budget uncertainty set (3), with budget $\Gamma\ge0$ and deviations $\hat d_j^t>0$. For every commitment $x$,
--   $$\max_{d\in\mathcal D}\ \sum_{t\in\mathcal T}\ \min_{p^t\in\Omega_t^{NR}(x,d^t)}\sum_{i\in\mathcal N_g}C_ip_i^t=\sum_{t\in\mathcal T}\ \max_{d^t\in\mathcal D^t}\ \min_{p^t\in\Omega_t^{NR}(x,d^t)}\sum_{i\in\mathcal N_g}C_ip_i^t .$$
--
--   The worst case over a product set of a sum of terms, each depending on one factor, is the sum of the worst cases. This is the second step of part (i) of the proof of Theorem 1.
--
--   **Formalization Note** Periods are `Fin T` with Lean period $t$ being the paper's period $t+1$. Net-load trajectories are $d:\{0,\dots,T-1\}\to\mathbb R^{N_d}$. Values are extended reals: a minimum over an empty set is $+\infty$ (an infeasible dispatch problem costs $+\infty$). The standing assumptions $\Gamma\ge 0$ and $\hat d^t_j>0$ of the budget set (3) are carried as hypotheses; they make $\bar d\in\mathcal D$, so every $\mathcal D^t$ is nonempty.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 11, Theorem 1, proof (i), second equality

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, proof (i), second equality, p. 11: the uncertainty set `𝒟 = ∏_t 𝒟^t` of (3) is
separable over time, so the worst case over `𝒟` of the sum of the per-period least dispatch costs
is the sum over periods of the per-period worst cases. -/
theorem two_stage_uncertainty_separable {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j)
    (x : Fin Ng → Fin T → ℝ) :
    (⨆ d ∈ uncSet dbar dhat Γ, ∑ t, ⨅ q ∈ OmegaNR D x t (d t), ((dispCost D q : ℝ) : EReal)) =
      ∑ t, perPeriodValue D (budgetSet dbar dhat Γ) x t := by sorry

end MultistageRUC.Equiv
