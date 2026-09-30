-- Prove2me | Theorems.Thm_MarkovChainChoice_Assortment_assortment_value_eq_lp_value
-- name    : MarkovChainChoice.Assortment.assortment_value_eq_lp_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:11:40.940669+00:00
-- url     : https://prove2.me/theorems/913f9677-127f-442d-8cf4-ec1ff756f800
-- title:
--   The optimal value of (Assortment) equals the optimal value of the linear program over $\mathcal H$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model on $N=\{1,\dots,n\}$ and $r\in\mathbb R^n$ revenues. The linear program
--
--   $$
--   \max_{(x,z)\in\mathbb R^{2n}_+}\Big\{\sum_{j\in N}r_jx_j:\ x_j+z_j=\lambda_j+\sum_{i\in N}\rho_{i,j}z_i\ \ \forall j\in N\Big\}
--   $$
--
--   has an optimal solution, and for every optimal solution $(x^\star,z^\star)$ of it and every optimal solution $S^\star$ of the assortment problem $\max_{S\subseteq N}\sum_{j\in N}P_{j,S}r_j$,
--
--   $$
--   \sum_{j\in N}P_{j,S^\star}r_j=\sum_{j\in N}r_jx^\star_j .
--   $$
--
--   So the optimal expected revenue over all $2^n$ offer sets is obtained by solving one linear program.
--
--   **Formalization Note.** Both optima are stated with attainment: the linear program's optimum is asserted to exist, and an optimal assortment always exists because there are finitely many offer sets.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Section 3, display following Lemma 1

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model
import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms

namespace MarkovChainChoice.Assortment

theorem assortment_value_eq_lp_value {n : ℕ} (M : Model n) (r : Fin n → ℝ) :
    (∃ p, IsLPOptimal M r p) ∧
    ∀ (S : Finset (Fin n)) (p : (Fin n → ℝ) × (Fin n → ℝ)),
      IsOptimalAssortment M r S → IsLPOptimal M r p → revenue M r S = lpObjective r p := by sorry

end MarkovChainChoice.Assortment
