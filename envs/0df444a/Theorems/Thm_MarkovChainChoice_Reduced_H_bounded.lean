-- Prove2me | Theorems.Thm_MarkovChainChoice_Reduced_H_bounded
-- name    : MarkovChainChoice.Reduced.H_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:33:27.954104+00:00
-- url     : https://prove2.me/theorems/c8456726-0cd5-41eb-844d-02ad1c18ac20
-- title:
--   Lemma 10 (as quoted in the proof of Theorem 7) — the polyhedron ℋ is bounded
-- statement:
--   For a Markov chain choice model with $\lambda_j>0$, $\rho_{j,i}\ge 0$ and $\sum_{i\in N}\rho_{j,i}<1$ for all $j$, the polyhedron
--   $$\mathcal H = \Big\{(x,z)\in\mathbb R^{2n}_+ :\ x_j + z_j = \lambda_j + \sum_{i\in N}\rho_{i,j} z_i\ \ \forall j\in N\Big\}$$
--   is a bounded subset of $\mathbb R^{2n}$.
--
--   Together with the fact that $\mathcal H$ is a polyhedron, boundedness makes $\mathcal H$ a polytope, so every point of it is a convex combination of its extreme points.
--
--   **Formalization Note** Boundedness is Mathlib's `Bornology.IsBounded` in the product space `(Fin n → ℝ) × (Fin n → ℝ)` (sup metric). The paper proves this lemma in its online appendix; the statement here is the one quoted in the proof of Theorem 7.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1331, proof of Theorem 7, second sentence (quoting Lemma 10 of Online Appendix D)

import Mathlib
import Definitions.Def_MarkovChainChoice_Reduced_Model
import Definitions.Def_MarkovChainChoice_Reduced_LinearPrograms

namespace MarkovChainChoice.Reduced

theorem H_bounded {n : ℕ} (M : Model n) : Bornology.IsBounded (H M) := by sorry

end MarkovChainChoice.Reduced
