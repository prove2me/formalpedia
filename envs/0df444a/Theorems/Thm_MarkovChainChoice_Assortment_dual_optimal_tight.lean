-- Prove2me | Theorems.Thm_MarkovChainChoice_Assortment_dual_optimal_tight
-- name    : MarkovChainChoice.Assortment.dual_optimal_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:12:31.534991+00:00
-- url     : https://prove2.me/theorems/f83ef375-f19e-4157-9a12-04848673f8e8
-- title:
--   An optimal solution of (Dual) is tight in one of its two constraints at every product
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model on $N=\{1,\dots,n\}$, $r\in\mathbb R^n$ revenues, and $\hat v$ an optimal solution of
--
--   $$
--   \min_{v\in\mathbb R^n}\Big\{\sum_{j\in N}\lambda_jv_j:\ v_j\ge r_j\ \ \forall j,\ \ v_j\ge\sum_{i\in N}\rho_{j,i}v_i\ \ \forall j\Big\}.
--   $$
--
--   Then for each $j\in N$,
--
--   $$
--   \hat v_j=r_j\qquad\text{or}\qquad \hat v_j=\sum_{i\in N}\rho_{j,i}\hat v_i .
--   $$
--
--   This complementary-slackness type property identifies, product by product, whether the dual solution is pinned by the revenue or by the continuation value.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, proof of Theorem 2, third sentence

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model
import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms

namespace MarkovChainChoice.Assortment

theorem dual_optimal_tight {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    ∀ j, v j = r j ∨ v j = ∑ i, M.rho j i * v i := by sorry

end MarkovChainChoice.Assortment
