-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_nested_step
-- name    : MultistageRUC.Equiv.nested_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:05.631015+00:00
-- url     : https://prove2.me/theorems/584772cc-befc-46b0-8aab-46428a805286
-- title:
--   Theorem 1, proof (ii), the t = T − 1 step, p. 12 — a stage's max-min splits off the later nested value
-- statement:
--   Let $\mathcal D^t$ be the budget sets (3) with $\Gamma\ge0$ and $\hat d_j^t>0$, and let $V_k$ denote the nested value of $(\widetilde M^{NR})$ from period $k$ to the end ($V_{T+1}=0$). Because $\mathcal D^{k+1},\dots$, $\Omega_{k+1}^{NR},\dots$ and the later costs do not depend on $p^k$ and $d^k$, for every period $k$
--   $$V_k=\max_{d^k\in\mathcal D^k}\ \min_{p^k\in\Omega_k^{NR}(x,d^k)}\big\{C^\top p^k+V_{k+1}\big\}=\Big(\max_{d^k\in\mathcal D^k}\ \min_{p^k\in\Omega_k^{NR}(x,d^k)}C^\top p^k\Big)+V_{k+1}.$$
--
--   The paper carries out this step at $t=T-1$ and then states that the argument is repeated backward; the statement here is that step at an arbitrary period, the form the backward induction uses.
--
--   **Formalization Note** Periods are `Fin T` with Lean period $t$ being the paper's period $t+1$. Net-load trajectories are $d:\{0,\dots,T-1\}\to\mathbb R^{N_d}$. Values are extended reals: a minimum over an empty set is $+\infty$ (an infeasible dispatch problem costs $+\infty$). The standing assumptions $\Gamma\ge 0$ and $\hat d^t_j>0$ of the budget set (3) are carried as hypotheses; they make $\bar d\in\mathcal D$, so every $\mathcal D^t$ is nonempty.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 12, Theorem 1, proof (ii), step at t = T − 1

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, proof (ii), the step at `t = T − 1`, p. 12, stated at every period `k`: since the later
stages do not depend on `p^k` and `d^k`, the max-min at stage `k` of `C^⊤p^k` plus the later nested
value splits into the per-period worst-case dispatch cost of stage `k` plus the later nested value. -/
theorem nested_step {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j)
    (x : Fin Ng → Fin T → ℝ) (k : ℕ) (hk : k < T) :
    nestedNR D (budgetSet dbar dhat Γ) x k =
      perPeriodValue D (budgetSet dbar dhat Γ) x ⟨k, hk⟩ +
        nestedNR D (budgetSet dbar dhat Γ) x (k + 1) := by sorry

end MultistageRUC.Equiv
