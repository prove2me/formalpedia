-- Prove2me | Theorems.Thm_OAI_LinearAlgebra_SpectralBooks_dual_exponent
-- name    : OAI.LinearAlgebra.SpectralBooks.dual_exponent
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T02:42:08.074897+00:00
-- url     : https://prove2.me/theorems/927d8394-51e1-5af0-827c-371ff1e0a774
-- title:
--   Dual matrix multiplication exponent equals $1/2$
-- statement:
--   For every field $F$, the dual exponent equals $1/2$:
--   $$
--   \alpha(F)=\frac12.
--   $$
--
--   Write $\omega(F;w_{12},w_{23},w_{31})$ for the formal arithmetic exponent at those three real weights, in the division-free model where additions, subtractions, and multiplications each cost $1$ and correctness is a polynomial identity. Define
--   $$
--   \alpha(F)=\sup\{t\in[0,1]:\omega(F;1,1,t)=2\}.
--   $$
--   The variable $t$ is the third weight $w_{31}$. The first two weights are fixed at $1$, so the formats in question have wire dimensions $\lceil N^{t}\rceil$, $N$, and $N$. Membership in the set requires exact equality of the exponent with $2$, not an inequality. The supremum is taken over the closed unit interval, endpoints included.
--
--   On $\mathbb{R}$, the supremum of the empty set is $0$. The equality $\alpha(F)=1/2$ therefore asserts both that the set is nonempty and that its least upper bound is $1/2$. The least upper bound need not itself lie in the set.
--
--   **Formalization note.** $\alpha(F)$ is obtained by applying the dual-exponent construction to the partially applied function $t\mapsto\omega(F;1,1,t)$. No continuity or monotonicity of that function is assumed in the definition.
-- source:
--   OpenAI math scope note lean/docs/107.md: the dual exponent, the supremum of t in [0,1] with omega(F;1,1,t)=2, is alpha(F)=1/2. Comparator: https://github.com/openai/math/blob/main/lean/ComparatorChallenges/MatrixExponent.lean#L110-L118 . Proved form: https://github.com/openai/math/blob/main/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean . Paper: https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf .

import Definitions.Def_OAI_SpectralBooks_MatrixExponent

set_option autoImplicit false

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The dual matrix multiplication exponent over every field. -/
theorem dual_exponent (F : Type*) [Field F] : formalAlpha F = (1 : ℝ) / 2 := by
  sorry

end SpectralBooks
end LinearAlgebra
end OAI
