-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_nested_eq_sum
-- name    : MultistageRUC.Equiv.nested_eq_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:18.811742+00:00
-- url     : https://prove2.me/theorems/85bb5c5e-0d4e-4719-92f9-f1895723d03a
-- title:
--   Theorem 1, proof (ii), backward induction, p. 12 — the nested value equals the sum of per-period worst cases
-- statement:
--   Let $\mathcal D^t$ be the budget sets (3) with $\Gamma\ge0$ and $\hat d_j^t>0$. For every commitment $x$,
--   $$\max_{d^1\in\mathcal D^1}\ \min_{p^1\in\Omega_1^{NR}(x,d^1)}\Big\{C^\top p^1+\cdots+\max_{d^T\in\mathcal D^T}\ \min_{p^T\in\Omega_T^{NR}(x,d^T)}C^\top p^T\Big\}=\sum_{t\in\mathcal T}\ \max_{d^t\in\mathcal D^t}\ \min_{p^t\in\Omega_t^{NR}(x,d^t)}C^\top p^t .$$
--
--   This is the conclusion of the backward induction in part (ii) of the proof of Theorem 1.
--
--   **Formalization Note** Periods are `Fin T` with Lean period $t$ being the paper's period $t+1$. Net-load trajectories are $d:\{0,\dots,T-1\}\to\mathbb R^{N_d}$. Values are extended reals: a minimum over an empty set is $+\infty$ (an infeasible dispatch problem costs $+\infty$). The standing assumptions $\Gamma\ge 0$ and $\hat d^t_j>0$ of the budget set (3) are carried as hypotheses; they make $\bar d\in\mathcal D$, so every $\mathcal D^t$ is nonempty.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 12, Theorem 1, proof (ii)

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, proof (ii), backward induction down to `t = 1`, p. 12: the nested value of
`(M̃^{NR})` from the first period equals `Σ_t max_{d^t ∈ 𝒟^t} min_{p^t ∈ Ω_t^{NR}(x, d^t)} C^⊤p^t`. -/
theorem nested_eq_sum {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j)
    (x : Fin Ng → Fin T → ℝ) :
    nestedNR D (budgetSet dbar dhat Γ) x 0 = ∑ t, perPeriodValue D (budgetSet dbar dhat Γ) x t := by sorry

end MultistageRUC.Equiv
