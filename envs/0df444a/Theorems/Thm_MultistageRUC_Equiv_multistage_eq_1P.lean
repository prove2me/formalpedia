-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_multistage_eq_1P
-- name    : MultistageRUC.Equiv.multistage_eq_1P
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:25.970151+00:00
-- url     : https://prove2.me/theorems/36524fd9-2bd3-4abe-869c-8a14da40e859
-- title:
--   Theorem 1, proof (ii), conclusion, p. 12 — without ramping, the multistage objective (5) equals the objective of (1P)
-- statement:
--   Let $\mathcal D$ be the budget uncertainty set (3) with $\Gamma\ge0$ and $\hat d_j^t>0$. For every commitment $(x,u,v)\in X$, the objective of the multistage robust UC (5) with the ramping constraints (5c) deleted equals the objective of problem (1P):
--   $$F(x)+\min_{p(\cdot)\ \text{non-anticipative, feasible}}\ \max_{d\in\mathcal D}\sum_t\sum_iC_ip_i^t(d^{[t]})=\sum_{t\in\mathcal T}\sum_{i\in\mathcal N_g}(G_ix_i^t+S_iu_i^t)+\sum_{t\in\mathcal T}\max_{d^t\in\mathcal D^t}\min_{p^t\in\Omega_t^{NR}(x,d^t)}\sum_iC_ip_i^t .$$
--
--   Minimizing both sides over $X$ shows that the multistage model without ramping is equivalent to (1P); this is part (ii) of the proof of Theorem 1.
--
--   **Formalization Note** Periods are `Fin T` with Lean period $t$ being the paper's period $t+1$. Net-load trajectories are $d:\{0,\dots,T-1\}\to\mathbb R^{N_d}$. Values are extended reals: a minimum over an empty set is $+\infty$ (an infeasible dispatch problem costs $+\infty$). The standing assumptions $\Gamma\ge 0$ and $\hat d^t_j>0$ of the budget set (3) are carried as hypotheses; they make $\bar d\in\mathcal D$, so every $\mathcal D^t$ is nonempty.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 12, Theorem 1, proof (ii), conclusion

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, proof (ii), conclusion, p. 12: without ramping constraints, the objective of the
multistage robust UC (5) at a commitment `(x, u, v) ∈ X` equals the objective of problem (1P). -/
theorem multistage_eq_1P {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j)
    (x u v : Fin Ng → Fin T → ℝ) (hX : InX D x u v) :
    multiStageObj D (uncSet dbar dhat Γ) false x u v = onePObj D (budgetSet dbar dhat Γ) x u := by sorry

end MultistageRUC.Equiv
