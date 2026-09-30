-- Prove2me | Theorems.Thm_MarkovChainChoice_Assortment_extreme_point_eq_balance
-- name    : MarkovChainChoice.Assortment.extreme_point_eq_balance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:10:56.148643+00:00
-- url     : https://prove2.me/theorems/9470519b-b3c2-4272-8dd7-a8773de5501a
-- title:
--   Lemma 1 — extreme points of $\mathcal H$ are the (Balance) solutions $(P_S,R_S)$
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model and $\mathcal H=\{(x,z)\in\mathbb R^{2n}_+: x_j+z_j=\lambda_j+\sum_{i\in N}\rho_{i,j}z_i\ \forall j\}$. For an extreme point $(\hat x,\hat z)$ of $\mathcal H$, let $S_{\hat x}=\{j\in N:\hat x_j>0\}$. Then
--
--   $$
--   P_{j,S_{\hat x}}=\hat x_j\quad\text{and}\quad R_{j,S_{\hat x}}=\hat z_j\qquad\text{for all } j\in N .
--   $$
--
--   Every vertex of $\mathcal H$ is therefore the purchase/non-purchase visit vector of some offer set, which is the bridge from the combinatorial assortment problem to linear programming.
--
--   **Formalization Note.** Extreme points are Mathlib's `Set.extremePoints ℝ (H M)` in `(Fin n → ℝ) × (Fin n → ℝ)`.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Lemma 1

import Mathlib
import Definitions.Def_MarkovChainChoice_Assortment_Model
import Definitions.Def_MarkovChainChoice_Assortment_LinearPrograms

namespace MarkovChainChoice.Assortment

theorem extreme_point_eq_balance {n : ℕ} (M : Model n) (x z : Fin n → ℝ)
    (hext : (x, z) ∈ Set.extremePoints ℝ (H M)) :
    ∀ j, purchase M (Finset.univ.filter (fun i => 0 < x i)) j = x j ∧
      visitNot M (Finset.univ.filter (fun i => 0 < x i)) j = z j := by sorry

end MarkovChainChoice.Assortment
