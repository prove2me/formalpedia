-- Prove2me | Theorems.Thm_LefebvreVariations_moore_bound_hoffman_singleton
-- name    : LefebvreVariations.moore_bound_hoffman_singleton
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:12:35.908936+00:00
-- url     : https://prove2.me/theorems/82f96f00-c2a7-59b9-b620-d0d943ba1c71
-- title:
--   Lefebvre's variations, No. 170 — on a theme by Hoffman–Singleton: the Moore bound is attained at degree 7 and girth 5 (Hoffman-Singleton graph)
-- statement:
--   $$\exists\, n\ \exists\, G \text{ on } [n]:\quad G\ \text{is }7\text{-regular},\ \operatorname{girth}(G)=5,\ n\le 1+7\sum_{i<(5-1)/2}(7-1)^i = 50.$$
--
--   The Hoffman--Singleton graph is a 7-regular graph on 50 vertices of girth 5, and $1+7(1+6)=50$ is the Moore bound for $(k,g)=(7,5)$.
--
--   **Formalization Note** The statement is the instance `(k, g) = (7, 5)` of `moore_bound_conjecture`, with `G : SimpleGraph (Fin n)`, `G.degree v = 7` for all `v`, `G.girth = 5` (the natural-number girth of Mathlib) and `n ≤ 1 + 7 * ∑ i ∈ Finset.range ((5 - 1) / 2), (7 - 1) ^ i`.
--
--   **Why this is a variation.** This is a variation of the platform problem moore_bound_conjecture (existence of a k-regular graph of odd girth g meeting the Moore bound). That parent is open on the platform; as far as I recall it is known to fail for most (k, g) (Moore graphs of odd girth g >= 7 do not exist, and for g = 5 only k in (2, 3, 7 or 57) survive, k = 57 being open) (cited from memory), so the point here is the instance where the conclusion is true. It is the case (k, g) = (7, 5) in the parent's own statement, an explicit finite graph a prover can supply and check.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. J. Hoffman and R. R. Singleton, 'On Moore graphs with diameters 2 and 3', IBM J. Res. Develop. 4 (1960), 497-504 (cited from memory). Regularity (7) and girth (5) of the explicit model with vertices P_h(i), Q_j(i) over Z/5 were verified by computer here.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Case `(k, g) = (7, 5)` of `moore_bound_conjecture`: the Hoffman–Singleton graph, 50 vertices, 7-regular, girth 5, and `1 + 7*(1+6) = 50`. An explicit model: vertices `P_h(i)`, `Q_j(i)` with `h, i, j` in `Z/5`, edges `P_h(i)~P_h(i+1)`, `Q_j(i)~Q_j(i+2)`, `P_h(i)~Q_j(h*j+i)`; regularity and girth were verified by computer.
Source: A. J. Hoffman and R. R. Singleton, "On Moore graphs with diameters 2 and 3", IBM J. Res. Develop. 4 (1960), 497-504 (cited from memory). -/
theorem moore_bound_hoffman_singleton :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      (∀ v : Fin n, G.degree v = 7) ∧
      G.girth = 5 ∧
      n ≤ 1 + 7 * ∑ i ∈ Finset.range ((5 - 1) / 2), (7 - 1) ^ i := by
  sorry

end LefebvreVariations
