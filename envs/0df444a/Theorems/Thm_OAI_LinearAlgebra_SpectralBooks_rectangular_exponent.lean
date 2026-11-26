-- Prove2me | Theorems.Thm_OAI_LinearAlgebra_SpectralBooks_rectangular_exponent
-- name    : OAI.LinearAlgebra.SpectralBooks.rectangular_exponent
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T02:42:56.692853+00:00
-- url     : https://prove2.me/theorems/5d38c2df-735e-41eb-975c-1de6136bb0bd
-- title:
--   Exact rectangular matrix multiplication exponent
-- statement:
--   For every field $F$ and all real weights $a,b,c$, with no sign restriction,
--   $$
--   \omega(F;a,b,c)
--   =
--   x+y+\frac{\bigl(\max(0,\ (x+y)z-xy)\bigr)^{2}}{4xyz},
--   $$
--   where $A=\max(a,0)$, $B=\max(b,0)$, $C=\max(c,0)$, the numbers $x\ge y\ge z$ are $A,B,C$ written in nonincreasing order, and $y=A+B+C-x-z$ is the middle value.
--
--   Here $\omega$ is the formal arithmetic exponent: the infimum of those $\tau$ for which every $\varepsilon>0$ admits a constant $C>0$ bounding the cost of a formally correct division-free program on the rounded shape $(\lceil N^{c}\rceil,\lceil N^{a}\rceil,\lceil N^{b}\rceil)$ by $C\, N^{\tau+\varepsilon}$, at every integer $N\ge 1$. Additions, subtractions, and multiplications each cost $1$. Correctness is a polynomial identity over $F$.
--
--   Real division is total, so a zero denominator makes the fraction $0$. That is the encoding of the rule that the correction term vanishes on the coordinate planes, not an extra hypothesis excluding those planes. Negative weights are replaced by $0$ before sorting. Substituting $(a,b,c)=(1,1,1)$ recovers $9/4$, but the statement is the identity at every real triple.
--
--   **Formalization note.** The weight order in $\omega(F;a,b,c)$ is $(w_{12},w_{23},w_{31})=(a,b,c)$. The real infimum of an empty or unbounded-below set is $0$, so the identity also rules out that junk value except where the displayed right-hand side is itself $0$.
-- source:
--   OpenAI math scope note lean/docs/107.md, the exact rectangular formula, extended by the comparator to every real weight by taking nonnegative parts. Comparator: https://github.com/openai/math/blob/main/lean/ComparatorChallenges/MatrixExponent.lean#L121-L131 . Proved form: https://github.com/openai/math/blob/main/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean . Scope: https://github.com/openai/math/blob/main/lean/docs/107.md .

import Definitions.Def_OAI_SpectralBooks_MatrixExponent

set_option autoImplicit false

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The exact rectangular exponent with the nonnegative parts of the weights sorted
in descending order. On coordinate planes the correction term is zero. -/
theorem rectangular_exponent (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c =
      let A := max a 0
      let B := max b 0
      let C := max c 0
      let x := max A (max B C)
      let z := min A (min B C)
      let y := A + B + C - x - z
      x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z) := by
  sorry

end SpectralBooks
end LinearAlgebra
end OAI
