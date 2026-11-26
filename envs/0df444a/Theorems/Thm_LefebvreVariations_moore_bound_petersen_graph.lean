-- Prove2me | Theorems.Thm_LefebvreVariations_moore_bound_petersen_graph
-- name    : LefebvreVariations.moore_bound_petersen_graph
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:12:17.1479+00:00
-- url     : https://prove2.me/theorems/d93c06ac-c93f-55be-95aa-2ee4ad6b7f31
-- title:
--   Lefebvre's variations, No. 168 — on a theme by Hoffman–Singleton: the Moore bound is attained at degree 3 and girth 5 (Petersen graph)
-- statement:
--   $$\exists\, n\ \exists\, G \text{ on } [n]:\quad G\ \text{is }3\text{-regular},\ \operatorname{girth}(G)=5,\ n\le 1+3\sum_{i<(5-1)/2}(3-1)^i = 10.$$
--
--   The Petersen graph is a 3-regular graph on 10 vertices of girth 5, and $1+3(1+2)=10$ is the Moore bound for $(k,g)=(3,5)$.
--
--   **Formalization Note** The statement is the instance `(k, g) = (3, 5)` of `moore_bound_conjecture`, with `G : SimpleGraph (Fin n)`, `G.degree v = 3` for all `v`, `G.girth = 5` (the natural-number girth of Mathlib) and `n ≤ 1 + 3 * ∑ i ∈ Finset.range ((5 - 1) / 2), (3 - 1) ^ i`.
--
--   **Why this is a variation.** This is a variation of the platform problem moore_bound_conjecture (existence of a k-regular graph of odd girth g meeting the Moore bound). That parent is open on the platform; as far as I recall it is known to fail for most (k, g) (Moore graphs of odd girth g >= 7 do not exist, and for g = 5 only k in (2, 3, 7 or 57) survive, k = 57 being open) (cited from memory), so the point here is the instance where the conclusion is true. It is the case (k, g) = (3, 5) in the parent's own statement, an explicit finite graph a prover can supply and check.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. J. Hoffman and R. R. Singleton, 'On Moore graphs with diameters 2 and 3', IBM J. Res. Develop. 4 (1960), 497-504 (cited from memory); the Petersen graph is the classical (3,5) Moore graph. Degree and girth of the standard 10-vertex model (outer 5-cycle, inner pentagram, spokes) verified by computer here.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The platform problem `moore_bound_conjecture` asks, for every degree `k ≥ 3` and odd girth `g ≥ 3`, for a `k`-regular graph of girth `g` with at most `1 + k * Σ_{i<(g-1)/2} (k-1)^i` vertices (a Moore graph). Case `(k, g) = (3, 5)`: the Petersen graph, 10 vertices, 3-regular, girth 5, and `1 + 3*(1+2) = 10`.
Source: Moore graphs, Hoffman and Singleton, "On Moore graphs with diameters 2 and 3", IBM J. Res. Develop. 4 (1960); the Petersen graph is the classical (3,5) Moore graph (cited from memory). -/
theorem moore_bound_petersen_graph :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      (∀ v : Fin n, G.degree v = 3) ∧
      G.girth = 5 ∧
      n ≤ 1 + 3 * ∑ i ∈ Finset.range ((5 - 1) / 2), (3 - 1) ^ i := by
  sorry

end LefebvreVariations
