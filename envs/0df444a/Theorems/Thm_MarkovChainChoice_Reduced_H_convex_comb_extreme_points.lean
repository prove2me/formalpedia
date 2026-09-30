-- Prove2me | Theorems.Thm_MarkovChainChoice_Reduced_H_convex_comb_extreme_points
-- name    : MarkovChainChoice.Reduced.H_convex_comb_extreme_points
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:34:00.214503+00:00
-- url     : https://prove2.me/theorems/38d45a96-facd-41a9-a71f-0214371451cc
-- title:
--   Proof of Theorem 7, p. 1331 — every point of ℋ is a positive convex combination of finitely many extreme points
-- statement:
--   Let $(\hat x,\hat z)\in\mathcal H$, where $\mathcal H$ is the polyhedron of the Markov chain choice model. Then there exist $K\ge 1$, extreme points $(x^1,z^1),\dots,(x^K,z^K)$ of $\mathcal H$, and positive scalars $\gamma^1,\dots,\gamma^K$ with $\sum_{k=1}^K\gamma^k = 1$ such that
--   $$\hat x = \sum_{k=1}^K\gamma^k x^k \qquad\text{and}\qquad \hat z = \sum_{k=1}^K \gamma^k z^k.$$
--
--   This is the representation of a point of the polytope $\mathcal H$ through its vertices; combined with Lemma 1 it expresses any point of $\mathcal H$ through the vectors $(P_S,R_S)$.
--
--   **Formalization Note** $K$ is a natural number and the extreme points and weights are indexed by `Fin K`; the condition $\sum_k\gamma^k = 1$ forces $K\ge 1$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1331, proof of Theorem 7, third sentence

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model
import Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms

namespace MarkovChainChoice.Reduced

theorem H_convex_comb_extreme_points {n : ℕ} (M : Model n) (x z : Fin n → ℝ)
    (hxz : (x, z) ∈ H M) :
    ∃ (K : ℕ) (p : Fin K → (Fin n → ℝ) × (Fin n → ℝ)) (γ : Fin K → ℝ),
      (∀ k, p k ∈ Set.extremePoints ℝ (H M)) ∧ (∀ k, 0 < γ k) ∧ ∑ k, γ k = 1 ∧
      x = ∑ k, γ k • (p k).1 ∧ z = ∑ k, γ k • (p k).2 := by sorry

end MarkovChainChoice.Reduced
