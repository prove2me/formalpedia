-- Prove2me | Theorems.Thm_IntMul_TM_schonhage_strassen
-- name    : IntMul.TM.schonhage_strassen
-- status  : Open
-- author  : @avi
-- created : 2026-10-09T02:11:24.698532+00:00
-- url     : https://prove2.me/theorems/c02939f1-fab9-47dd-9229-99cc9b1e1686
-- title:
--   Schönhage–Strassen: multiplication in time $O(n\log n\log\log n)$ on a multitape Turing machine
-- statement:
--   **Schönhage–Strassen.** There is a single deterministic multitape Turing machine that, for every $n\ge1$ and all $x,y\in\{0,1\}^n$, halts on input $x\#y$ with output $\operatorname{bin}_{2n}(\operatorname{val}x\cdot\operatorname{val}y)$, and whose worst-case running time on $n$-bit inputs is
--   $$O\big(n\log n\log\log n\big).$$
--
--   This was the fastest known multiplication algorithm from 1971 until Fürer (2007), and it is the standard fast multiplier underlying the fixed-point arithmetic of later algorithms. In Harvey–van der Hoeven it supplies the crude bound $\mathsf M(n)=O(n^{1+\delta})$ with $\delta<\frac18$ (§2.1).
--
--   **Formalization Note** The machine model is the shared `IntMul_MultitapeModel` (Montanaro's $k$-tape conventions: read-only input tape, output tape, $\triangleright$ only in cell $0$, $\mathrm{START}\ne\mathrm{HALT}$, frozen halting state). $O(\cdot)$ means a bound $c\,g(n)$ for all $n\ge n_0$, with $c>0$ and $n_0$ depending only on the machine; sizes $1\le n<n_0$ need only correctness. The logarithms are natural; since $\log\log n\le0$ for $n\le2$, a valid threshold has $n_0\ge3$.
-- source:
--   A. Schönhage, V. Strassen, Schnelle Multiplikation großer Zahlen, Computing 7 (1971), 281–292 (main result: multiplication of n-digit numbers on multitape Turing machines in O(n log n log log n) steps); see also Brent–Zimmermann, Modern Computer Arithmetic (2011), §2.3.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

namespace IntMul.TM

theorem schonhage_strassen :
    MulTimeBound fun n => (n : ℝ) * Real.log n * Real.log (Real.log n) := by sorry

end IntMul.TM
