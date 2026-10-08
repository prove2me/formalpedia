-- Prove2me | Theorems.Thm_LeightonRao_Uniform_lemma_6
-- name    : LeightonRao.Uniform.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:13.857119+00:00
-- url     : https://prove2.me/theorems/c4ee47e7-df5e-48ce-8c17-5396d2e1dbc5
-- title:
--   Lemma 6, p. 800 — a distance function satisfying (5) yields a cut of ratio cost ≤ 36W log n
-- statement:
--   Let $G$ be a connected network on $n\ge2$ nodes and $d$ a distance function with total weight $W$ that satisfies the distance constraint $\sum_{\{u,v\}}d(u,v)\ge1$. Then there is a nonempty proper subset $U\subset V$ with
--   $$\frac{C(U,\bar U)}{|U|\,|\bar U|}\le 36\,W\log n .$$
--
--   Combined with the existence of a distance function with $W=f$ (LP duality), this gives the lower half of Theorem 2.
--
--   **Formalization Note** The page states "ratio cost $O(W\log n)$". The constant $36$ comes from the proof on p. 800: it takes Corollary 4's bound $36W\log n$ or Lemma 5's bound $6W$, and $6W\le36W\log n$ since $\log n\ge1$ for $n\ge2$. Connectivity is the paper's standing assumption (p. 789).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 800, Lemma 6 (constant from Corollary 4 and Lemma 5)

import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Lemma 6, p. 800, with the factor `36` from Corollary 4 and Lemma 5. -/
theorem lemma_6 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hconstraint : SatisfiesDistanceConstraint N d) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ratioCost N U ≤ 36 * totalWeight N d * Real.logb 2 (Fintype.card V : ℝ) := by sorry

end LeightonRao.Uniform
