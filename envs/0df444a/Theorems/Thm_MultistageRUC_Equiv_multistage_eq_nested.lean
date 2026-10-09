-- Prove2me | Theorems.Thm_MultistageRUC_Equiv_multistage_eq_nested
-- name    : MultistageRUC.Equiv.multistage_eq_nested
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:57.596997+00:00
-- url     : https://prove2.me/theorems/89b19a99-956c-43dc-9254-262e3402fa2a
-- title:
--   Theorem 1, proof (ii), first step, pp. 10–11 — without ramping, the multistage objective (5) equals the nested value of (M̃^NR)
-- statement:
--   Let $\mathcal D$ be the budget uncertainty set (3) with $\Gamma\ge0$ and $\hat d_j^t>0$. For every commitment $(x,u,v)\in X$, the objective of the multistage robust UC (5) with the ramping constraints (5c) deleted — the commitment cost plus the least worst-case dispatch cost over non-anticipative policies $p^t(d^{[t]})$ that satisfy (5b), (5d), (5e) for every $d\in\mathcal D$ — equals the commitment cost plus the nested value
--   $$\max_{d^1\in\mathcal D^1}\ \min_{p^1\in\Omega_1^{NR}(x,d^1)}\Big\{C^\top p^1+\cdots+\max_{d^T\in\mathcal D^T}\ \min_{p^T\in\Omega_T^{NR}(x,d^T)}C^\top p^T\Big\}$$
--   of $(\widetilde M^{NR})$.
--
--   The paper obtains this from its remark (p. 10) that (5) is equivalently represented by the nested formulation (6), together with $\Omega_t(x,d^t,p^{t-1})=\Omega_t^{NR}(x,d^t)$ when the ramping constraints are absent.
--
--   **Formalization Note** Periods are `Fin T` with Lean period $t$ being the paper's period $t+1$. Net-load trajectories are $d:\{0,\dots,T-1\}\to\mathbb R^{N_d}$. Values are extended reals: a minimum over an empty set is $+\infty$ (an infeasible dispatch problem costs $+\infty$). The standing assumptions $\Gamma\ge 0$ and $\hat d^t_j>0$ of the budget set (3) are carried as hypotheses; they make $\bar d\in\mathcal D$, so every $\mathcal D^t$ is nonempty. A policy is a function of the period and of the whole trajectory; non-anticipativity requires that $p^t(d)=p^t(d')$ whenever $d^s=d'^s$ for all $s\le t$.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, pp. 10–11, Theorem 1, proof (ii), (6) and (M̃^NR)

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace MultistageRUC.Equiv

/-- Theorem 1, proof (ii), first step, pp. 10–11: without ramping constraints, the objective of the
multistage robust UC (5) at a commitment `(x, u, v) ∈ X` equals the commitment cost plus the nested
value of `(M̃^{NR})`. -/
theorem multistage_eq_nested {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j)
    (x u v : Fin Ng → Fin T → ℝ) (hX : InX D x u v) :
    multiStageObj D (uncSet dbar dhat Γ) false x u v =
      ((commitCost D x u : ℝ) : EReal) + nestedNR D (budgetSet dbar dhat Γ) x 0 := by sorry

end MultistageRUC.Equiv
