-- Prove2me | Theorems.Thm_OAI_RationalHitting_Generator_list_hits
-- name    : OAI.RationalHitting.Generator.list_hits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:17:12.044255+00:00
-- url     : https://prove2.me/theorems/be8b5df2-b59d-4d5a-8bef-314403486f92
-- title:
--   The cyclotomic grid list hits every admissible nonzero rational formula of size at most s (OpenAI rational hitting lists, Proposition 5.1)
-- statement:
--   **Notation** (the published bundle `Def_RationalHitting` and the definitions bundle `OAIQWRHT000` of this split). A formula in $n$ variables (`Formula n`) is built from variables, rational constants, sums, products and unary inverses, and its size counts nodes. It evaluates at a tuple $X$ of $n$ rational $d \times d$ matrices to $v$ (`Evaluates f X v`) when an inverse node is evaluated only at an operand with a two-sided inverse. A formula is admissible if some tuple of positive dimension evaluates it, and nonzero if some such evaluation is a nonzero matrix. An `Output n` is a positive dimension $d$ with a list of $n$-tuples of $d \times d$ rational matrices. `Hits s H` says that every admissible nonzero formula of size at most $s$ has, at some tuple of $H$, a value that is an invertible matrix.
--
--   The list `Generator.list n s` is OpenAI's explicit construction. Parameters $N$, $e$ and $H$ are fixed functions of $n$ and $s$ (`Parameters.N`, `Parameters.exponent`, `Parameters.H`). For each point $x$ of the grid $\{1, \dots, H\}^3$, matrices $Z_0(x), \dots, Z_n(x)$ over the cyclotomic ring of order $2^{e+1}$ are written as rational matrices of dimension $D = 2^{e+1} \cdot 2^e$ (`Generator.Z`, `Generator.D`). When $\det Z_0(x) \neq 0$, the list contains the tuple $\bigl(Z_0(x)^{-1} Z_1(x), \dots, Z_0(x)^{-1} Z_n(x)\bigr)$ (`Generator.atPoint`, `Generator.tupleAt`).
--
--   **The statement.** For all $n$ and all $s \ge 1$, `Hits s (Generator.list n s)`: every admissible nonzero formula in $n$ variables of size at most $s$ has a defined and invertible value at some tuple of the list.
--
--   This is the paper's Proposition 5.1 for the list it constructs.
--
--   Lean: `OAI.RationalHitting.Generator.list_hits`, OpenAI's theorem of that name (in `lean/OAI/Computability/RationalHitting/Generator.lean`).
-- source:
--   OpenAI, Polynomial Hitting Lists for Noncommutative Rational Formulas, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 116; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/RationalHitting/Generator.lean (declaration OAI.RationalHitting.Generator.list_hits)

import Mathlib
import Definitions.Def_RationalHitting
import Definitions.Def_OAIQWRHT000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.Generator
noncomputable section

theorem list_hits (n s : ℕ) (hs : 1 ≤ s) : Hits s (list n s) := by
  sorry

end
end RationalHitting.Generator

end OAI
end
