-- Prove2me | Theorems.Thm_OAI_PermanentBorder_permanent_exact_cubic_lower_bound
-- name    : OAI.PermanentBorder.permanent_exact_cubic_lower_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T19:51:52.308983+00:00
-- url     : https://prove2.me/theorems/43512877-b220-461a-ab45-bbba8d38e115
-- title:
--   An exact determinantal representation of the m × m permanent has size at least m³/(5529600 e) (OpenAI permanent, Theorem 1.1)
-- statement:
--   **Notation** (published bundle `Def_PermanentCubic`). `permanentPolynomial m` is the $m \times m$ permanent $\sum_{\tau} \prod_i X_{i,\tau(i)}$ in the $m^2$ variables $X_{i,j}$ over $\mathbb C$. An exact determinantal representation of size $n$ (`HasExactDeterminant n p`) is $n > 0$ together with complex $n \times n$ matrices $A_0$ and $A_v$, one per variable $v$, with $\det\bigl(A_0 + \sum_v v\,A_v\bigr) = p$. A border representation of size $n$ (`HasBorderDeterminant n p`) is $n > 0$ together with sequences of such matrices, indexed by $j \in \mathbb N$, such that every coefficient of $\det\bigl(A_0(j) + \sum_v v\,A_v(j)\bigr)$ converges to the corresponding coefficient of $p$ as $j \to \infty$.
--
--   **The statement.** For all $m \ge 1408$ and $n$, if the $m \times m$ permanent has an exact determinantal representation of size $n$, then
--   $$\frac{m^3}{5529600\, e} \;\le\; n.$$
--
--   This is the second component of the goal `OAI.PermanentBorder.permanent_cubic_lower_bounds`; the paper's Theorem 1.1 notes that the same bound holds for exact determinantal complexity.
--
--   Lean: `OAI.PermanentBorder.permanent_exact_cubic_lower_bound`, OpenAI's theorem of that name (in `lean/OAI/Algebra/Determinantal/Main.lean`).
-- source:
--   OpenAI, A cubic lower bound for border determinantal complexity of the permanent, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 108; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf, Theorem 1.1; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/Determinantal/Main.lean (declaration OAI.PermanentBorder.permanent_exact_cubic_lower_bound)

import Mathlib
import Definitions.Def_PermanentCubic

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial

theorem permanent_exact_cubic_lower_bound (m n : ℕ) (hm : 1408 ≤ m)
    (h : HasExactDeterminant n (permanentPolynomial m)) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ) := by
  sorry

end PermanentBorder

end OAI
end
