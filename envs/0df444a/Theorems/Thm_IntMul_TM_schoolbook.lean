-- Prove2me | Theorems.Thm_IntMul_TM_schoolbook
-- name    : IntMul.TM.schoolbook
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T02:06:28.184987+00:00
-- url     : https://prove2.me/theorems/86109c88-e1e4-410a-a312-0a5f005a04cf
-- title:
--   Schoolbook multiplication in time $O(n^2)$ on a multitape Turing machine
-- statement:
--   **Schoolbook multiplication.** There is a single deterministic multitape Turing machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}x\cdot\operatorname{val}y)$, and whose worst-case running time on $n$-bit inputs is $O(n^2)$.
--
--   This is the classical shift-and-add algorithm; on a multitape machine each of the $n$ shifted additions costs $O(n)$ steps.
--
--   **Formalization Note** The machine model is the shared `IntMul_MultitapeModel` (Montanaro's $k$-tape conventions: read-only input tape, output tape, $\triangleright$ only in cell $0$, $\mathrm{START}\ne\mathrm{HALT}$, frozen halting state). $O(\cdot)$ means a bound $c\,g(n)$ for all $n\ge n_0$, with $c>0$ and $n_0$ depending only on the machine; sizes $1\le n<n_0$ need only correctness.
-- source:
--   Folklore; see R. P. Brent, P. Zimmermann, Modern Computer Arithmetic, Cambridge Univ. Press 2011, §1.3.1 (naive multiplication); D. E. Knuth, TAOCP Vol. 2, 3rd ed., §4.3.1 Algorithm M.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.TM

theorem schoolbook : MulTimeBound fun n => (n : ℝ) ^ 2 := by sorry

end IntMul.TM
