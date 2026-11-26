-- Prove2me | Theorems.Thm_LefebvreVariations_sunflower_two_three
-- name    : LefebvreVariations.sunflower_two_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:56:23.767092+00:00
-- url     : https://prove2.me/theorems/4e5ca428-3eb4-4a24-b6f0-954ad90f518b
-- title:
--   Lefebvre's variations, No. 24 — on a theme by Erdős and Rado: the sunflower number $f(2,3)=7$
-- statement:
--   This is the first non-trivial exact value of the Erdős–Rado sunflower function.
--
--   A $k$-sunflower is a family of $k$ distinct sets whose pairwise intersections are all equal. Let $f(n,k)$ be the least $m$ such that every family of $m$ distinct $n$-element sets contains a $k$-sunflower. Then
--
--   $$
--   f(2,3)=7 .
--   $$
--
--   Six edges forming two disjoint triangles contain no three edges through a common vertex and no three pairwise disjoint edges, hence no $3$-sunflower. Conversely, among any seven distinct edges either some vertex lies on three of them (a sunflower with a one-point kernel) or every vertex lies on at most two, and then three pairwise disjoint edges can be found (a sunflower with empty kernel).
--
--   The sunflower problem (Erdős Problem 20) asks whether $f(n,k)\le C_k^{\,n}$; Erdős and Rado proved $(k-1)^n<f(n,k)\le n!\,(k-1)^n+1$. Exact values are known only for very small parameters.
--
--   **Formalization Note** The function is the mission's `Erdos20.f`, defined as an infimum over all families of $n$-sets in an arbitrary ground type, with sunflowers of cardinality exactly $k$.
--
--   **Why this is a variation.** This varies the Erdős sunflower problem (Erdős Problem 20, `Erdos20.erdos_20`), which asks whether $f(n,k)\le C_k^{\,n}$. It is the first non-trivial size, $n=2$ and $k=3$: the exact value $f(2,3)=7$, where a family of $2$-element sets is a graph. Settling it fixes the first exact value of $f(n,k)$ beyond the trivial cases, against which the Erdős–Rado bounds $(k-1)^n<f(n,k)\le n!\,(k-1)^n+1$ can be checked.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   P. Erdős and R. Rado, Intersection theorems for systems of sets, J. London Math. Soc. 35 (1960), 85–90 (sunflower lemma and the bounds (k−1)^n < f(n,k) ≤ n!(k−1)^n + 1); the value f(2,3) = 7 is the elementary graph case (a family of 7 edges has 3 edges through a vertex or 3 pairwise disjoint edges, while two disjoint triangles have neither). Problem page: https://www.erdosproblems.com/20. Parent problem: Erdos20.erdos_20 (sunflower conjecture).

import Mathlib
import Definitions.Def_Erdos20_defs

namespace LefebvreVariations

/-- The sunflower problem (Erdős Problem 20) at its first non-trivial size: the exact
value `f(2,3) = 7`. A family of `2`-element sets is a "graph", and a `3`-sunflower in it
is either three edges through one vertex (kernel of size `1`) or three pairwise
disjoint edges (empty kernel). Two disjoint triangles give `6` edges with no
`3`-sunflower, and any `7` edges contain one (maximum degree `≤ 2` and matching number
`≤ 2` force at most `6` edges).
Source: Erdős and Rado, "Intersection theorems for systems of sets", J. London Math. Soc.
35 (1960), 85-90, where `f(n,k)` is introduced and `(k-1)^n < f(n,k) ≤ n!(k-1)^n + 1`;
the value `f(2,3) = 7` is listed with the other small values in Abbott and Hanson,
"A problem of Schur and its generalizations", Acta Arith. 20 (1972), 175-187, and at
https://www.erdosproblems.com/20. -/
theorem sunflower_two_three : Erdos20.f 2 3 = 7 := by
  sorry

end LefebvreVariations
