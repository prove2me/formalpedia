-- Prove2me | Theorems.Thm_OAI_LinearAlgebra_SpectralBooks_square_exponent
-- name    : OAI.LinearAlgebra.SpectralBooks.square_exponent
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T02:41:37.831286+00:00
-- url     : https://prove2.me/theorems/f14be80a-b0a8-4cc0-af03-7ba7a9ce4f6a
-- title:
--   Square matrix multiplication exponent equals $9/4$
-- statement:
--   For every field $F$, the formal arithmetic exponent of square matrix multiplication equals $9/4$:
--   $$
--   \omega(F;1,1,1)=\frac94.
--   $$
--
--   The exponent $\omega(F;w_{12},w_{23},w_{31})$ is the infimum of the real numbers $\tau$ with the following property. For every $\varepsilon>0$ there is a constant $C>0$ such that, for every integer $N\ge 1$, the product of two $N\times N$ matrices over $F$ is computed by some division-free straight-line program of cost at most $C\, N^{\tau+\varepsilon}$. The program's inputs are independent indeterminates. Each output register must carry the corresponding entry of the product as a polynomial identity, not merely as a function on $F$. The cost counts every addition, every subtraction, and every multiplication; constants and inputs are free. There is no division gate.
--
--   The three weights in the goal are the real numbers $1,1,1$, in the order $(w_{12},w_{23},w_{31})$. At those weights every wire dimension equals $N$, so the claim is about square shapes only. The equality identifies the infimum. It is not an upper bound. On $\mathbb{R}$, the infimum of an empty set, or of a set that is not bounded below, is the junk value $0$; the statement says that the infimum is $9/4$ rather than that junk value.
--
--   **Formalization note.** The field $F$ is an arbitrary field: every universe, every characteristic, and every cardinality. The quantifier on the scale starts at $N=1$, so the empty scale $N=0$ is not part of the exponent.
-- source:
--   OpenAI, The matrix multiplication exponent is nine fourths, 24 November 2026, the square-exponent theorem. Lean statement: https://github.com/openai/math/blob/main/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean#L11-L12 . Comparator: https://github.com/openai/math/blob/main/lean/ComparatorChallenges/MatrixExponent.lean#L106-L107 . Scope: https://github.com/openai/math/blob/main/lean/docs/107.md .

import Definitions.Def_OAI_SpectralBooks_MatrixExponent

set_option autoImplicit false

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The square matrix multiplication exponent over every field. -/
theorem square_exponent (F : Type*) [Field F] : formalOmega F 1 1 1 = (9 : ℝ) / 4 := by
  sorry

end SpectralBooks
end LinearAlgebra
end OAI
