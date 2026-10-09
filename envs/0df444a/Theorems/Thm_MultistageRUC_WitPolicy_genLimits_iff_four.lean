-- Prove2me | Theorems.Thm_MultistageRUC_WitPolicy_genLimits_iff_four
-- name    : MultistageRUC.WitPolicy.genLimits_iff_four
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:14:39.766404+00:00
-- url     : https://prove2.me/theorems/4ba7d70e-9773-4d73-aa79-ec9da97fd954
-- title:
--   Proposition 6, proof of (i), pp. ec1–ec2 — robust generation limits under the W_it-policy are four deterministic inequalities
-- statement:
--   Let $\mathcal D=\prod_t\mathcal D^t$ be the budget uncertainty set (3), and let $\mathbf d_{\max},\mathbf d_{\min}\in\mathcal D$ be trajectories whose total load is maximal, respectively minimal, over $\mathcal D$ in every period ((19), (20)). Write $L_{\max}=\sum_j d^t_{\max,j}$ and $L_{\min}=\sum_j d^t_{\min,j}$ for their total loads in period $t$.
--
--   Fix a generator $i$ and a period $t$, and consider the $W_{it}$-policy $p^t_i(\mathbf d)=w^t_i+W_{it}\sum_j d^t_j$. The robust generation limits (8c),
--   $$p^{\min}_i x^t_i\le w^t_i+W_{it}\Big(\sum_{j\in\mathcal N_d}d^t_j\Big)\le p^{\max}_i x^t_i\qquad\forall\,\mathbf d\in\mathcal D,$$
--   hold if and only if the four inequalities
--   $$p^{\min}_i x^t_i\le w^t_i+W_{it}L_{\max}\le p^{\max}_i x^t_i,\qquad p^{\min}_i x^t_i\le w^t_i+W_{it}L_{\min}\le p^{\max}_i x^t_i$$
--   hold.
--
--   This is the computational content of part (i) of Proposition 6: a semi-infinite family of constraints, one per load trajectory, collapses to four deterministic linear constraints in $(w^t_i,W_{it},x^t_i)$.
--
--   **Formalization Note.** Lean periods are 0-based. The commitment $x^t_i$ is an arbitrary real. The scenarios are hypotheses: any trajectories in $\mathcal D$ that maximize, respectively minimize, the total load of every period.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, pp. ec1–ec2 (PDF pp. 34–35), Proof of Proposition 6, part (i)

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

namespace MultistageRUC.WitPolicy

theorem genLimits_iff_four {Ng Nd T : ℕ}
    (pmin pmax : Fin Ng → ℝ) (x w W : Fin Ng → Fin T → ℝ)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (dmax dmin : Fin T → Fin Nd → ℝ)
    (hmax : IsMaxLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmax)
    (hmin : IsMinLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmin) (i : Fin Ng) (t : Fin T) :
    GenLimits pmin pmax x w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
      (pmin i * x i t ≤ w i t + W i t * totalLoad dmax t ∧
          w i t + W i t * totalLoad dmax t ≤ pmax i * x i t) ∧
        (pmin i * x i t ≤ w i t + W i t * totalLoad dmin t ∧
          w i t + W i t * totalLoad dmin t ≤ pmax i * x i t) := by sorry

end MultistageRUC.WitPolicy
