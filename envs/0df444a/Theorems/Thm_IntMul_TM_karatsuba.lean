-- Prove2me | Theorems.Thm_IntMul_TM_karatsuba
-- name    : IntMul.TM.karatsuba
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T02:07:57.608232+00:00
-- url     : https://prove2.me/theorems/20e14722-d831-42ed-b103-0aeafc07f8f5
-- title:
--   Karatsuba–Ofman: multiplication in time $O(n^{\log_2 3})$ on a multitape Turing machine
-- statement:
--   **Karatsuba–Ofman multiplication.** There is a single deterministic multitape Turing machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}x\cdot\operatorname{val}y)$, and whose worst-case running time on $n$-bit inputs is
--   $$O\big(n^{\log_2 3}\big)\approx O(n^{1.585}).$$
--
--   The algorithm splits each operand into two halves and replaces four half-size products by three, giving the recurrence $\mathsf M(n)\le3\mathsf M(\lceil n/2\rceil+1)+O(n)$.
--
--   **Formalization Note** The machine model is the shared `IntMul_MultitapeModel` (Montanaro's $k$-tape conventions: read-only input tape, output tape, $\triangleright$ only in cell $0$, $\mathrm{START}\ne\mathrm{HALT}$, frozen halting state). $O(\cdot)$ means a bound $c\,g(n)$ for all $n\ge n_0$, with $c>0$ and $n_0$ depending only on the machine; sizes $1\le n<n_0$ need only correctness.
-- source:
--   A. Karatsuba, Yu. Ofman, Multiplication of multidigit numbers on automata, Soviet Physics Doklady 7 (1963), 595–596; see also Brent–Zimmermann, Modern Computer Arithmetic (2011), §1.3.2.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.TM

theorem karatsuba : MulTimeBound fun n => (n : ℝ) ^ Real.logb 2 3 := by sorry

end IntMul.TM
