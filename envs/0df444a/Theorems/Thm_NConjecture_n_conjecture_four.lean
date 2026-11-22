-- Prove2me | Theorems.Thm_NConjecture_n_conjecture_four
-- name    : NConjecture.n_conjecture_four
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T00:45:45.696564+00:00
-- url     : https://prove2.me/theorems/d2d194a3-1666-4b8f-b47a-82a70e476dfc
-- title:
--   The $n$-conjecture for quadruples ($n=4$)
-- statement:
--   The $n=4$ instance of the Browkin–Brzeziński $n$-conjecture (the "abcd conjecture"): for every $\varepsilon>0$ there is $C>0$ such that every admissible quadruple $(a_1,a_2,a_3,a_4)$ of integers — summing to zero, with setwise gcd $1$ and no vanishing nonempty proper subsum — satisfies
--   $$\max_i|a_i|\le C\,\operatorname{rad}(a_1a_2a_3a_4)^{\,3+\varepsilon}.$$
--   This is the first open case beyond abc and an intermediate target toward the full conjecture; by the propagation theorem it already implies abc. The exponent $3=2\cdot4-5$ is sharp (Browkin–Brzeziński Theorem 1).
--
--   **Formalization Note.** This is `conjAt 4` exactly, with all predicates from `NConjecture_Defs`.
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf §2 p. 933 (the n-conjecture, n=4 instance). Discussed in R. Hölzl, S. Kleine, F. Stephan, Improved lower bounds for strong n-conjectures, arXiv:2409.13439v2 (2025). https://arxiv.org/abs/2409.13439 Remark 5(2) p. 3 (Q_A(4) ≤ 3).

import Mathlib
import Definitions.Def_NConjecture_Defs

namespace NConjecture

theorem n_conjecture_four : conjAt 4 := by sorry

end NConjecture
