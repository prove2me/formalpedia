-- Prove2me | Theorems.Thm_MarkovChainChoice_Assortment_dual_value_eq_lp_value
-- name    : MarkovChainChoice.Assortment.dual_value_eq_lp_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:12:09.590475+00:00
-- url     : https://prove2.me/theorems/4d96bebc-7b97-43f1-b233-b0d07f006665
-- title:
--   (Dual) has an optimal solution and its value equals that of the linear program over $\mathcal H$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model on $N=\{1,\dots,n\}$ and $r\in\mathbb R^n$ revenues. The problem
--
--   $$
--   \min_{v\in\mathbb R^n}\Big\{\sum_{j\in N}\lambda_jv_j:\ v_j\ge r_j\ \ \forall j\in N,\ \ v_j\ge\sum_{i\in N}\rho_{j,i}v_i\ \ \forall j\in N\Big\}\qquad\text{(Dual)}
--   $$
--
--   has an optimal solution, and for every optimal solution $\hat v$ of (Dual) and every optimal solution $(x^\star,z^\star)$ of the linear program $\max\{\sum_j r_jx_j:(x,z)\in\mathcal H\}$,
--
--   $$
--   \sum_{j\in N}\lambda_j\hat v_j=\sum_{j\in N}r_jx^\star_j .
--   $$
--
--   (Dual) is the linear programming dual of the program over $\mathcal H$; this is strong duality for that pair.
--
--   **Formalization Note.** Optimality on both sides is "feasible and at least as good as every feasible point".
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Section 3, display (Dual)

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model
import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms

namespace MarkovChainChoice.Assortment

theorem dual_value_eq_lp_value {n : ℕ} (M : Model n) (r : Fin n → ℝ) :
    (∃ v, IsDualOptimal M r v) ∧
    ∀ (v : Fin n → ℝ) (p : (Fin n → ℝ) × (Fin n → ℝ)),
      IsDualOptimal M r v → IsLPOptimal M r p → ∑ j, M.lam j * v j = lpObjective r p := by sorry

end MarkovChainChoice.Assortment
