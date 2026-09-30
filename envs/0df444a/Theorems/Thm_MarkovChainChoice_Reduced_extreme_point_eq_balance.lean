-- Prove2me | Theorems.Thm_MarkovChainChoice_Reduced_extreme_point_eq_balance
-- name    : MarkovChainChoice.Reduced.extreme_point_eq_balance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:32:21.845327+00:00
-- url     : https://prove2.me/theorems/c2fe151c-db4f-4f6f-a603-61152a45a537
-- title:
--   Lemma 1 — an extreme point (x̂, ẑ) of ℋ equals (P_S, R_S) for S = {j : x̂_j > 0}
-- statement:
--   Let $(\hat x,\hat z)$ be an extreme point of the polyhedron
--   $$\mathcal H = \Big\{(x,z)\in\mathbb R^{2n}_+ :\ x_j + z_j = \lambda_j + \sum_{i\in N}\rho_{i,j} z_i\ \ \forall j\in N\Big\},$$
--   and let $S_{\hat x} = \{j\in N : \hat x_j > 0\}$ be the support of $\hat x$. Then
--   $$P_{j,S_{\hat x}} = \hat x_j \quad\text{and}\quad R_{j,S_{\hat x}} = \hat z_j \qquad\text{for all } j\in N.$$
--
--   Every extreme point of $\mathcal H$ is therefore the purchase/non-purchase visit vector of some offer set, which links the geometry of $\mathcal H$ to assortments.
--
--   **Formalization Note** Extreme points are Mathlib's `Set.extremePoints ℝ (H M)` in the product space `(Fin n → ℝ) × (Fin n → ℝ)`; the support is `Finset.univ.filter (fun i => 0 < x i)`.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Lemma 1

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model
import Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms

namespace MarkovChainChoice.Reduced

theorem extreme_point_eq_balance {n : ℕ} (M : Model n) (x z : Fin n → ℝ)
    (hext : (x, z) ∈ Set.extremePoints ℝ (H M)) :
    ∀ j, purchase M (Finset.univ.filter (fun i => 0 < x i)) j = x j ∧
      visitNot M (Finset.univ.filter (fun i => 0 < x i)) j = z j := by sorry

end MarkovChainChoice.Reduced
