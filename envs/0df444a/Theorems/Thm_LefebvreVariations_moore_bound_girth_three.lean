-- Prove2me | Theorems.Thm_LefebvreVariations_moore_bound_girth_three
-- name    : LefebvreVariations.moore_bound_girth_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:12:57.085852+00:00
-- url     : https://prove2.me/theorems/c92e05a6-df55-4aa8-8b32-957f1f03cea5
-- title:
--   Lefebvre's variations, No. 171 — on a theme by Hoffman–Singleton: the Moore bound is attained at girth 3 for every degree k at least 3
-- statement:
--   $$\forall k\ge 3\ \exists n\ \exists G\text{ on }[n]:\quad G\ k\text{-regular},\ \operatorname{girth}(G)=3,\ n\le 1+k\sum_{i<1}(k-1)^i=k+1.$$
--
--   For every degree $k\ge3$ the complete graph $K_{k+1}$ is $k$-regular of girth $3$ and meets the Moore bound $k+1$ with equality. This is the case $g=3$ of the Moore bound problem.
--
--   **Formalization Note** The statement is `moore_bound_conjecture` with `g = 3` fixed and `k ≥ 3` universally quantified; `G.girth` is Mathlib's natural-number girth, and `(3 - 1) / 2 = 1`.
--
--   **Why this is a variation.** This is a variation of the platform problem moore_bound_conjecture (existence of a k-regular graph of odd girth g meeting the Moore bound). That parent is open on the platform; as far as I recall it is known to fail for most (k, g) (Moore graphs of odd girth g >= 7 do not exist, and for g = 5 only k in (2, 3, 7 or 57) survive, k = 57 being open) (cited from memory), so the point here is the instance where the conclusion is true. It is the case g = 3, every k >= 3, of the parent's own statement: the complete graph K_{k+1}, an easy infinite family that gives the base of the odd-girth case.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Elementary: K_{k+1} is k-regular with triangles (k >= 2). Moore graphs and the Moore bound: Hoffman and Singleton, IBM J. Res. Develop. 4 (1960) (cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Girth `g = 3` of `moore_bound_conjecture`, every degree `k ≥ 3`: the complete graph on `k + 1` vertices is `k`-regular, has girth 3 and `k + 1 = 1 + k * (k-1)^0` vertices, i.e. it meets the Moore bound with equality. This is the trivial odd-girth case; the cases `g = 5` (Petersen, Hoffman–Singleton) are the only others where the conjecture's conclusion is known. -/
theorem moore_bound_girth_three (k : ℕ) (hk : 3 ≤ k) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (hD : DecidableRel G.Adj),
      (∀ v : Fin n, G.degree v = k) ∧
      G.girth = 3 ∧
      n ≤ 1 + k * ∑ i ∈ Finset.range ((3 - 1) / 2), (k - 1) ^ i := by
  sorry

end LefebvreVariations
