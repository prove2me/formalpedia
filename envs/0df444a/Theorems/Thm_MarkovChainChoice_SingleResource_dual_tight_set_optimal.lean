-- Prove2me | Theorems.Thm_MarkovChainChoice_SingleResource_dual_tight_set_optimal
-- name    : MarkovChainChoice.SingleResource.dual_tight_set_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:16:48.718892+00:00
-- url     : https://prove2.me/theorems/bed0ab50-dc77-4344-8fcf-190508e15b8e
-- title:
--   Theorem 2 — the tight set $\{j : \hat v_j = r_j\}$ of an optimal dual solution is an optimal assortment
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model with the standing assumptions and let $r\in\mathbb R^n$ be arbitrary product revenues. Let $\hat v$ be an optimal solution of the (Dual) linear program
--   $$\min_{v\in\mathbb R^n}\Big\{\sum_{j\in N}\lambda_j v_j : v_j\ge r_j,\ v_j\ge\sum_{i\in N}\rho_{j,i}v_i\ \ \forall j\in N\Big\},$$
--   and define $\hat S=\{j\in N:\hat v_j=r_j\}$. Then $\hat S$ is an optimal solution of the (Assortment) problem:
--   $$\sum_{j\in N}P_{j,S}\,r_j\ \le\ \sum_{j\in N}P_{j,\hat S}\,r_j\qquad\text{for every } S\subseteq N.$$
--
--   The theorem reduces assortment optimization under the Markov chain choice model to a linear program. In the single-resource problem it is applied in each period with the adjusted revenues $r_j-\Delta V_{t+1}(x)$, which may be negative.
--
--   **Formalization Note** The statement holds for every optimal $\hat v$ (the paper speaks of "the" optimal solution; no uniqueness is assumed). No sign condition is placed on $r$. This is the goal theorem of the companion mission I of this series, restated here because draft items cannot import one another.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Theorem 2

import Mathlib
import Definitions.Def_MarkovChainChoice_SingleResource_Assortment
open MarkovChainChoice.Shared

namespace MarkovChainChoice.SingleResource

theorem dual_tight_set_optimal {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    IsOptimalAssortment M r (Finset.univ.filter (fun j => v j = r j)) := by sorry

end MarkovChainChoice.SingleResource
