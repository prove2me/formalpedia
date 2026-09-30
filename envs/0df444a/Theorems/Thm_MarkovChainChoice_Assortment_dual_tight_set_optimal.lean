-- Prove2me | Theorems.Thm_MarkovChainChoice_Assortment_dual_tight_set_optimal
-- name    : MarkovChainChoice.Assortment.dual_tight_set_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:13:06.440976+00:00
-- url     : https://prove2.me/theorems/98cdbd8e-41a0-4d91-9000-63d99c0e0670
-- title:
--   Theorem 2 — the products with $\hat v_j=r_j$ form an optimal assortment
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model on $N=\{1,\dots,n\}$ (with $\lambda_j>0$, $\rho_{j,i}\ge0$, $\sum_i\rho_{j,i}<1$) and $r\in\mathbb R^n$ revenues. Let $\hat v$ be an optimal solution of
--
--   $$
--   \min_{v\in\mathbb R^n}\Big\{\sum_{j\in N}\lambda_jv_j:\ v_j\ge r_j\ \ \forall j\in N,\ \ v_j\ge\sum_{i\in N}\rho_{j,i}v_i\ \ \forall j\in N\Big\}\qquad\text{(Dual)}
--   $$
--
--   and define $\hat S=\{j\in N:\hat v_j=r_j\}$. Then $\hat S$ is an optimal solution of the assortment problem:
--
--   $$
--   \sum_{j\in N}P_{j,S}\,r_j\ \le\ \sum_{j\in N}P_{j,\hat S}\,r_j\qquad\text{for every } S\subseteq N,
--   $$
--
--   where $(P_S,R_S)$ is the solution of the (Balance) equations for the offer set $S$.
--
--   The assortment problem over $2^n$ offer sets is thereby solved by one linear program with $n$ variables, which makes it tractable.
--
--   **Formalization Note.** The theorem is stated for every optimal solution $\hat v$ of (Dual) (the paper's "the optimal solution"; the proof uses only optimality). $\hat S$ is defined by equality $\hat v_j=r_j$, and revenues carry no sign assumption.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Theorem 2

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model
import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms

namespace MarkovChainChoice.Assortment

theorem dual_tight_set_optimal {n : ℕ} (M : Model n) (r v : Fin n → ℝ)
    (hv : IsDualOptimal M r v) :
    IsOptimalAssortment M r (Finset.univ.filter (fun j => v j = r j)) := by sorry

end MarkovChainChoice.Assortment
