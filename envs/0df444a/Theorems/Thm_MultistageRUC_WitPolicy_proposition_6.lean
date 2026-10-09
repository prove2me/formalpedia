-- Prove2me | Theorems.Thm_MultistageRUC_WitPolicy_proposition_6
-- name    : MultistageRUC.WitPolicy.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:04.135287+00:00
-- url     : https://prove2.me/theorems/6ee10c77-db09-4fce-8b86-f74142b3cfa1
-- title:
--   Proposition 6, pp. 18–19 — under the W_it-policy, robust generation and ramping limits reduce to the extreme total-load scenarios
-- statement:
--   Consider the affine multistage robust unit commitment model under the $W_{it}$-policy $p^t_i(\mathbf d)=w^t_i+W_{it}\sum_{j\in\mathcal N_d}d^t_j$, with arbitrary output limits $p^{\min}_i,p^{\max}_i$, ramp rates $RD^t_i,RU^t_i,SD^t_i,SU^t_i$, commitments $x^t_i,u^t_i,v^t_i$, initial state $x^0_i,p^0_i$, and policy coefficients $w^t_i,W_{it}$. Let $\mathcal D=\prod_t\mathcal D^t$ be the budget uncertainty set (3), and let $\mathbf d_{\max},\mathbf d_{\min}\in\mathcal D$ be trajectories whose total load is maximal, respectively minimal, over $\mathcal D$ in every period ((19), (20)). Let $\mathbf d_{minmax}(t)$ and $\mathbf d_{maxmin}(t)$ be the scenarios (21), (22).
--
--   Then for every generator $i$ and every period $t$:
--   1. the robust generation limits (8c) over $\mathcal D$ are equivalent to the same constraints over the finite set $\{\mathbf d_{\min},\mathbf d_{\max}\}$;
--   2. the robust ramping-down limits (8d) at $t$ over $\mathcal D$ are equivalent to the same constraints over $\{\mathbf d_{\min},\mathbf d_{\max},\mathbf d_{minmax}(t),\mathbf d_{maxmin}(t)\}$, and so are the robust ramping-up limits (8e).
--
--   In symbols, for (8c),
--   $$p^{\min}_i x^t_i\le p^t_i(\mathbf d)\le p^{\max}_i x^t_i\ \ \forall\mathbf d\in\mathcal D\iff p^{\min}_i x^t_i\le p^t_i(\mathbf d)\le p^{\max}_i x^t_i\ \ \forall\mathbf d\in\{\mathbf d_{\min},\mathbf d_{\max}\}.$$
--
--   This is Proposition 6 of the paper. It means that, under the $W_{it}$-policy, the generation and ramping constraints can be imposed in advance through finitely many scenarios, so that only the worst-case cost constraint and the transmission constraints need constraint generation.
--
--   **Formalization Note.** The statement is for the $W_{it}$-policy; the $W_i$-policy (9) ("any simpler policy") is the instance $W_{it}=W_i$. Lean periods are 0-based. At the first period the ramping constraints compare with the initial dispatch $p^0_i$ and use $x^0_i$ in place of $x^{t-1}_i$. The commitments are arbitrary reals (the paper's $\{0,1\}$ restriction is not needed). The scenarios $\mathbf d_{\max},\mathbf d_{\min}$ are hypotheses: any members of $\mathcal D$ that maximize, respectively minimize, the total load of every period. The standing assumptions $\Gamma\ge0$, $\hat d^t_j>0$ of (3) are not needed once $\mathbf d_{\max},\mathbf d_{\min}\in\mathcal D$ is assumed, and are omitted.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, pp. 18–19, Proposition 6

import Mathlib
import Definitions.Def_MultistageRUC_WitPolicy_Setting

namespace MultistageRUC.WitPolicy

theorem proposition_6 {Ng Nd T : ℕ}
    (pmin pmax : Fin Ng → ℝ) (RD RU SD SU : Fin Ng → Fin T → ℝ)
    (x0 p0 : Fin Ng → ℝ) (x u v : Fin Ng → Fin T → ℝ) (w W : Fin Ng → Fin T → ℝ)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ)
    (dmax dmin : Fin T → Fin Nd → ℝ)
    (hmax : IsMaxLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmax)
    (hmin : IsMinLoad (MultistageRUC.Equiv.uncSet dbar dhat Γ) dmin) :
    ∀ i t,
      (GenLimits pmin pmax x w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
        GenLimits pmin pmax x w W {dmin, dmax} i t) ∧
      ((RampDown RD SD x v p0 w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
          RampDown RD SD x v p0 w W {dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} i t) ∧
        (RampUp RU SU x0 x u p0 w W (MultistageRUC.Equiv.uncSet dbar dhat Γ) i t ↔
          RampUp RU SU x0 x u p0 w W {dmin, dmax, dminmax dmin dmax t, dmaxmin dmin dmax t} i t)) := by sorry

end MultistageRUC.WitPolicy
