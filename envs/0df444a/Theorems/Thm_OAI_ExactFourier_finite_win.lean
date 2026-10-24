-- Prove2me | Theorems.Thm_OAI_ExactFourier_finite_win
-- name    : OAI.ExactFourier.finite_win
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:04:17.359059+00:00
-- url     : https://prove2.me/theorems/3cccfe05-acb8-4f51-bab1-5e7b1f972160
-- title:
--   Theorem 8.3 (Existence of a finite win): some tensor power of an invertible nonmonomial matrix is computed with fewer than b·q^(b-1) calls (OpenAI exact Fourier circuits)
-- statement:
--   The paper's Theorem 8.3, *Existence of a finite win*, as OpenAI formalized it; an intermediate statement of the split of OpenAI's proof that exact discrete Fourier transforms have circuits of size $o(n \log n)$ along a sequence of lengths (`OAI.ExactFourier.main_theorem`, the paper's Theorem 1.1).
--
--   **Notation** (published bundle `Def_ExactFourier` and definitions bundle `OAIQWEXF000` of this split). A matrix is monomial (`IsMonomial`, `MonomialMatrix`) when it is a permutation matrix times an invertible diagonal matrix. A matrix price (`MatrixPrice`) is a function $p$ assigning a real number $p(A)$ to every complex square matrix, indexed by any finite type, such that for invertible matrices: $p(A) \ge 0$ with equality exactly for monomial $A$; $p$ is unchanged by reindexing, by multiplying by monomial matrices on either side, by inversion and by transposition; $p(AB) \le p(A) + p(B)$; $p(A \oplus B) = p(A) + p(B)$; $p(A \otimes B) = |\kappa|\,p(A) + |\iota|\,p(B)$ for $A$ on $\iota$ and $B$ on $\kappa$; and $p$ of the $2 \times 2$ elementary transvection $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ is $1$.
--
--   **The statement** (`FiniteWinStatement`). There are $q$, an invertible matrix $A \in \mathrm{GL}_q(\mathbb C)$ that is not monomial, an integer $b \ge 2$ and a word $W$ on $q^b$ coordinates, each step of which is either a monomial matrix or a call of $A$ on an ordered $q$-tuple of distinct coordinates (`WordStep`), such that the product of the steps of $W$ (in order) equals the $b$-th Kronecker tensor power of $A$ (`tensorPower`) and the number of calls in $W$ is less than $b\,q^{b-1}$, the number the standard tensor-axis algorithm uses.
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf, Theorem 8.3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/GraphBlocks.lean (declaration OAI.ExactFourier.finite_win)

import Mathlib
import Definitions.Def_OAIQWEXF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier
theorem finite_win : FiniteWinStatement := by
  sorry
end ExactFourier

end
end

end OAI
end
