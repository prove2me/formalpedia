-- Prove2me | Theorems.Thm_MultistageRUC_WitPolicy_ramp_lhs_separable
-- name    : MultistageRUC.WitPolicy.ramp_lhs_separable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:28.765553+00:00
-- url     : https://prove2.me/theorems/1c7fe3d3-4b5a-4c12-93e5-79c1f7c86be9
-- title:
--   Proposition 6, proof of (ii), (23)–(24), p. 19 — the worst-case ramp of the W_it-policy separates over periods t−1 and t
-- statement:
--   Let $\mathcal D=\prod_t\mathcal D^t$ be the budget uncertainty set (3), with $\Gamma\ge0$ and $\hat d^t_j>0$ for all $t,j$. Fix a generator $i$, coefficients $W_{it}$ of the $W_{it}$-policy, and two consecutive periods $t-1$ and $t$.
--
--   The left-hand side of the robust ramping-up constraint written as (23), namely the worst-case change of the load-dependent part of the dispatch, separates over the two periods:
--   $$\max_{\mathbf d\in\mathcal D}\Big\{W_{it}\Big(\sum_{j\in\mathcal N_d}d^t_j\Big)-W_{i,t-1}\Big(\sum_{j\in\mathcal N_d}d^{t-1}_j\Big)\Big\}=\max_{\mathbf d^t\in\mathcal D^t}\Big\{W_{it}\sum_{j\in\mathcal N_d}d^t_j\Big\}-\min_{\mathbf d^{t-1}\in\mathcal D^{t-1}}\Big\{W_{i,t-1}\sum_{j\in\mathcal N_d}d^{t-1}_j\Big\}.$$
--
--   This is display (24) of the paper. It reflects that $\mathcal D$ is a product over periods, so the loads of periods $t-1$ and $t$ can be chosen independently by the adversary.
--
--   **Formalization Note.** The two sides are suprema and infima taken in the extended reals `EReal`. The hypotheses $\Gamma\ge0$ and $\hat d^t_j>0$ are the standing assumptions of (3): they make every $\mathcal D^t$ nonempty (it contains $\bar{\mathbf d}^t$) and bounded, so every extremum is finite and attained, and the subtraction never meets $\pm\infty$. The periods are Lean indices `s`, `t` with `t = s + 1`, so the statement concerns the paper's periods $t\ge2$.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, p. 19, Proof of Proposition 6, (23)–(24)

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

namespace MultistageRUC.WitPolicy

theorem ramp_lhs_separable {Ng Nd T : ℕ}
    (W : Fin Ng → Fin T → ℝ) (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j)
    (i : Fin Ng) (s t : Fin T) (hst : t.val = s.val + 1) :
    (⨆ d ∈ MultistageRUC.Equiv.uncSet dbar dhat Γ,
        ((W i t * totalLoad d t - W i s * totalLoad d s : ℝ) : EReal)) =
      (⨆ e ∈ MultistageRUC.Equiv.budgetSet dbar dhat Γ t, ((W i t * ∑ j, e j : ℝ) : EReal)) -
        (⨅ e ∈ MultistageRUC.Equiv.budgetSet dbar dhat Γ s, ((W i s * ∑ j, e j : ℝ) : EReal)) := by sorry

end MultistageRUC.WitPolicy
