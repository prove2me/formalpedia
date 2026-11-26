-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_three_eight_ge_28
-- name    : LefebvreVariations.ramsey_three_eight_ge_28
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:42:22.988802+00:00
-- url     : https://prove2.me/theorems/107d2a9c-6fe0-4e25-9c37-e978a2d4e543
-- title:
--   Lefebvre's variations, No. 100 — on a theme by Erdős: the Ramsey number R(3,8) is at least 28
-- statement:
--   $$R(3,8)\ \ge\ 28.$$
--
--   That is, there is a graph on $27$ vertices with no triangle and no independent set of $8$ vertices; equivalently, the edges of $K_{27}$ can be coloured red and blue with no red $K_3$ and no blue $K_8$.
--
--   The exact value is $R(3,8)=28$, so this is the sharp lower bound; the upper bound is a separate statement obtained by a large computation.
--
--   **Formalization Note** The statement is `28 ≤ Erdos77.asymmetricRamsey 3 8` in the platform definitions `Def_Erdos77_asymmetric_ramsey`, where `asymmetricRamsey k ℓ` is the least `n` such that every `SimpleGraph (Fin n)` has a `k`-clique or its complement has an `ℓ`-clique.
--
--   **Why this is a variation.** This is a variation of Erdős Problem 77 on the platform (does $R(k)^{1/k}$ have a limit), stated through that problem's asymmetric Ramsey numbers. It is a partial result at a small explicit size: the sharp lower bound $R(3,8)\ge 28$ in the parent's own definition `Erdos77.asymmetricRamsey`, certified by one explicit $27$-vertex graph. Settling it provides another concrete extremal graph for the family $R(3,k)$ whose growth the parent studies.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Small Ramsey numbers: S. P. Radziszowski, Small Ramsey Numbers, Electronic Journal of Combinatorics, Dynamic Survey DS1 (table of R(3,k)); R(3,8)=28 is due to McKay and Zhang (1992) (attribution cited from memory, not re-checked). The lower bound rests on a triangle-free graph on 27 vertices with independence number 7; one was found by a SAT solver and verified by exhaustive brute force while preparing this statement (94 edges, no triangle, no independent 8-set). Origin: an off-diagonal case of the asymmetric Ramsey numbers of the platform problem Erdos77 (limit of R(k)^(1/k)), stated in its own definitions.

import Definitions.Def_Erdos77_asymmetric_ramsey

set_option autoImplicit false

namespace LefebvreVariations

/-- Lower half of `R(3,8) = 28`: there is a triangle-free graph on `27` vertices with no
independent set of size `8`, so `R(3,8) ≥ 28`. The value `R(3,8)=28` is due to McKay and
Zhang (1992); see Radziszowski, "Small Ramsey numbers", Electronic J. Combin. Dynamic Survey
DS1 (cited from memory). A witness graph was found by a SAT solver and checked by brute force
in the course of preparing this statement. -/
theorem ramsey_three_eight_ge_28 : 28 ≤ Erdos77.asymmetricRamsey 3 8 := by
  sorry

end LefebvreVariations
