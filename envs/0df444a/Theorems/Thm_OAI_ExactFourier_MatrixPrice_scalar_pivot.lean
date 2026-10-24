-- Prove2me | Theorems.Thm_OAI_ExactFourier_MatrixPrice_scalar_pivot
-- name    : OAI.ExactFourier.MatrixPrice.scalar_pivot
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:04:00.270844+00:00
-- url     : https://prove2.me/theorems/7cb54085-fd97-426f-a1d8-8c4614273347
-- title:
--   A matrix price is invariant under a scalar pivot of an invertible block matrix (OpenAI exact Fourier circuits)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of `OAI.ExactFourier.main_theorem` (the paper's Theorem 1.1), used in the proof of the paper's Theorem 8.3 (`OAI.ExactFourier.finite_win`): pivoting on a $1 \times 1$ invertible corner does not change a matrix price.
--
--   **Notation** (published bundle `Def_ExactFourier` and definitions bundle `OAIQWEXF000` of this split). A matrix is monomial (`IsMonomial`, `MonomialMatrix`) when it is a permutation matrix times an invertible diagonal matrix. A matrix price (`MatrixPrice`) is a function $p$ assigning a real number $p(A)$ to every complex square matrix, indexed by any finite type, such that for invertible matrices: $p(A) \ge 0$ with equality exactly for monomial $A$; $p$ is unchanged by reindexing, by multiplying by monomial matrices on either side, by inversion and by transposition; $p(AB) \le p(A) + p(B)$; $p(A \oplus B) = p(A) + p(B)$; $p(A \otimes B) = |\kappa|\,p(A) + |\iota|\,p(B)$ for $A$ on $\iota$ and $B$ on $\kappa$; and $p$ of the $2 \times 2$ elementary transvection $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ is $1$.
--
--   **The statement.** Let $p$ be a matrix price, $A$ an invertible square matrix on a finite type $\alpha$, $C$ a column, $B$ a row and $D$ an invertible $1 \times 1$ matrix such that the block matrix $K = \begin{pmatrix} A & C \\ B & D\end{pmatrix}$ is invertible. Then the pivoted matrix (`Pivot.matrix A C B D`)
--   $$\begin{pmatrix} A - CD^{-1}B & CD^{-1} \\ -D^{-1}B & D^{-1}\end{pmatrix}$$
--   has the same price as $K$.
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf, Section 7; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/PivotJoin.lean (declaration OAI.ExactFourier.MatrixPrice.scalar_pivot)

import Mathlib
import Definitions.Def_OAIQWEXF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ExactFourier.MatrixPrice
variable {α : Type} [Fintype α] [DecidableEq α]

theorem scalar_pivot (p : MatrixPrice) (A : Matrix α α ℂ)
    (C : Matrix α PUnit ℂ) (B : Matrix PUnit α ℂ) (D : Matrix PUnit PUnit ℂ)
    (hA : IsUnit A) (hD : IsUnit D) (hK : IsUnit (Matrix.fromBlocks A C B D)) :
    p.value (Pivot.matrix A C B D)=p.value (Matrix.fromBlocks A C B D) := by
  sorry

end ExactFourier.MatrixPrice

end

end OAI
end
