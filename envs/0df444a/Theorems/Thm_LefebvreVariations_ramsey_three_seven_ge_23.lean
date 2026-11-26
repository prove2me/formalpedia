-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_three_seven_ge_23
-- name    : LefebvreVariations.ramsey_three_seven_ge_23
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:34:33.22444+00:00
-- url     : https://prove2.me/theorems/ba5a6468-7ab1-56ce-a2e6-c61c2dd49b0a
-- title:
--   Lefebvre's variations, No. 95 — on a theme by Erdős: the Ramsey number R(3,7) is at least 23
-- statement:
--   $$R(3,7)\ \ge\ 23.$$
--
--   That is, there is a graph on $22$ vertices with no triangle and no independent set of $7$ vertices; equivalently, the edges of $K_{22}$ can be coloured red and blue with no red $K_3$ and no blue $K_7$.
--
--   The exact value is $R(3,7)=23$, so this is the sharp lower bound; the matching upper bound is a separate, much harder statement.
--
--   **Formalization Note** The statement is `23 ≤ Erdos77.asymmetricRamsey 3 7` in the platform definitions `Def_Erdos77_asymmetric_ramsey`, where `asymmetricRamsey k ℓ` is the least `n` such that every `SimpleGraph (Fin n)` has a `k`-clique or its complement has an `ℓ`-clique.
--
--   **Why this is a variation.** This is a variation of Erdős Problem 77 on the platform (does $R(k)^{1/k}$ have a limit), stated through that problem's asymmetric Ramsey numbers. It is a partial result at a small explicit size: the sharp lower bound $R(3,7)\ge 23$ in the parent's own definition `Erdos77.asymmetricRamsey`, certified by one explicit $22$-vertex graph. Settling it supplies a concrete extremal construction of the kind the asymptotic question is built from.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Small Ramsey numbers: S. P. Radziszowski, Small Ramsey Numbers, Electronic Journal of Combinatorics, Dynamic Survey DS1 (table of R(3,k)); R(3,7)=23 is due to Grinstead and Roberts (1982) (attribution cited from memory, not re-checked). The lower bound rests on a triangle-free graph on 22 vertices with independence number 6; one was found by a SAT solver and verified by exhaustive brute force while preparing this statement (64 edges, no triangle, no independent 7-set). Origin: an off-diagonal case of the asymmetric Ramsey numbers of the platform problem Erdos77 (limit of R(k)^(1/k)), stated in its own definitions.

import Definitions.Def_Erdos77_asymmetric_ramsey

set_option autoImplicit false

namespace LefebvreVariations

/-- Lower half of `R(3,7) = 23`: there is a triangle-free graph on `22` vertices with no
independent set of size `7`, so `R(3,7) ≥ 23`. The exact value `R(3,7)=23` is due to
Grinstead and Roberts (1982); see Radziszowski, "Small Ramsey numbers", Electronic J. Combin.
Dynamic Survey DS1 (cited from memory). A witness graph was found by a SAT solver and
checked by brute force in the course of preparing this statement. -/
theorem ramsey_three_seven_ge_23 : 23 ≤ Erdos77.asymmetricRamsey 3 7 := by
  sorry

end LefebvreVariations
