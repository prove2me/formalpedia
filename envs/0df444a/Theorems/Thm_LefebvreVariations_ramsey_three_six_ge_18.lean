-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_three_six_ge_18
-- name    : LefebvreVariations.ramsey_three_six_ge_18
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:25:24.422082+00:00
-- url     : https://prove2.me/theorems/a4bed31d-a2cd-44e4-ae77-0eb97e11a910
-- title:
--   Lefebvre's variations, No. 82 — on a theme by Erdős: the Ramsey number R(3,6) is at least 18
-- statement:
--   $$R(3,6)\ \ge\ 18.$$
--
--   That is, there is a graph on $17$ vertices that contains no triangle and no independent set of $6$ vertices; equivalently, the edges of $K_{17}$ can be coloured red and blue so that there is no red $K_3$ and no blue $K_6$.
--
--   This is the first off-diagonal Ramsey number $R(3,k)$ beyond the classical values $R(3,3)=6$, $R(3,4)=9$, $R(3,5)=14$. The exact value is $R(3,6)=18$; the missing upper bound $R(3,6)\le 18$ is a separate, harder statement.
--
--   **Formalization Note** The statement is `18 ≤ Erdos77.asymmetricRamsey 3 6` in the platform definitions `Def_Erdos77_asymmetric_ramsey`, where `asymmetricRamsey k ℓ` is the least `n` such that every `SimpleGraph (Fin n)` has a `k`-clique or its complement has an `ℓ`-clique. It is a lower bound, so it needs exactly a `17`-vertex graph with no `3`-clique and whose complement has no `6`-clique.
--
--   **Why this is a variation.** This is a variation of Erdős Problem 77 on the platform, the open question of whether $R(k)^{1/k}$ has a limit, stated through the asymmetric Ramsey numbers of that problem. It is a first non-trivial size: the lower bound $R(3,6)\ge 18$ in the parent's own definition `Erdos77.asymmetricRamsey`, a finite explicit graph a prover can exhibit and check. Such small exact lower bounds are the base cases for the explicit constructions used to attack growth of Ramsey numbers.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Small Ramsey numbers: S. P. Radziszowski, Small Ramsey Numbers, Electronic Journal of Combinatorics, Dynamic Survey DS1 (the table of R(3,k)); R(3,6)=18 is due to Kalbfleisch (1966, lower bound) and Graver and Yackel (1968, upper bound) (attributions cited from memory, not re-checked). The lower bound R(3,6) >= 18 rests on a triangle-free graph on 17 vertices with independence number 5; one was found by a SAT solver and verified by exhaustive brute force while preparing this statement (41 edges, no triangle, no independent 6-set). Origin: the first non-trivial off-diagonal case of the asymmetric Ramsey numbers of the platform problem Erdos77 (limit of R(k)^(1/k)), stated in its own definitions.

import Definitions.Def_Erdos77_asymmetric_ramsey

set_option autoImplicit false

namespace LefebvreVariations

/-- Lower half of `R(3,6) = 18`: there is a triangle-free graph on `17` vertices with no
independent set of size `6`, so `R(3,6) ≥ 18`. This is the first non-trivial off-diagonal
case `R(3,k)` beyond the classical values `R(3,3)=6`, `R(3,4)=9`, `R(3,5)=14` (the value `R(3,6)=18` is due to
Kalbfleisch 1966 for the lower bound and Graver–Yackel 1968 for the upper bound).
Source: Radziszowski, "Small Ramsey numbers", Electronic J. Combin.
Dynamic Survey DS1 (cited from memory). A witness graph was found by a SAT solver and
checked by brute force in the course of preparing this statement. -/
theorem ramsey_three_six_ge_18 : 18 ≤ Erdos77.asymmetricRamsey 3 6 := by
  sorry

end LefebvreVariations
