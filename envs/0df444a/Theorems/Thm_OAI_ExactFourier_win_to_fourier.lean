-- Prove2me | Theorems.Thm_OAI_ExactFourier_win_to_fourier
-- name    : OAI.ExactFourier.win_to_fourier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:05:57.921686+00:00
-- url     : https://prove2.me/theorems/bda936ec-13b2-4463-a2f9-d9e2d561e92f
-- title:
--   A finite win gives exact Fourier circuits of size below c·n·log₂ n for every c > 0 along unbounded lengths (OpenAI exact Fourier circuits)
-- statement:
--   The reduction of the paper's Section 3 ("From a finite win to exact Fourier circuits"), as OpenAI formalized it; an intermediate statement of the split of OpenAI's proof of `OAI.ExactFourier.main_theorem` (the paper's Theorem 1.1).
--
--   **Notation** (published bundle `Def_ExactFourier` and definitions bundle `OAIQWEXF000` of this split). A matrix is monomial (`IsMonomial`, `MonomialMatrix`) when it is a permutation matrix times an invertible diagonal matrix. A matrix price (`MatrixPrice`) is a function $p$ assigning a real number $p(A)$ to every complex square matrix, indexed by any finite type, such that for invertible matrices: $p(A) \ge 0$ with equality exactly for monomial $A$; $p$ is unchanged by reindexing, by multiplying by monomial matrices on either side, by inversion and by transposition; $p(AB) \le p(A) + p(B)$; $p(A \oplus B) = p(A) + p(B)$; $p(A \otimes B) = |\kappa|\,p(A) + |\iota|\,p(B)$ for $A$ on $\iota$ and $B$ on $\kappa$; and $p$ of the $2 \times 2$ elementary transvection $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ is $1$.
--
--   **The statement.** If a finite win exists (`FiniteWinStatement`, as in the paper's Theorem 8.3: an invertible nonmonomial $A \in \mathrm{GL}_q(\mathbb C)$ and $b \ge 2$ with a word of monomial steps and calls of $A$ computing $A^{\otimes b}$ with fewer than $b q^{b-1}$ calls), then `MainStatement` holds: for every $c > 0$ and every $N_0 \ge 2$ there are $n \ge N_0$ and a linear circuit on $n$ inputs computing the unnormalized discrete Fourier matrix $(\omega^{jk})_{j,k}$ of order $n$ with fewer than $c\,n\log_2 n$ gates, where additions, subtractions and multiplications by fixed complex scalars each cost one gate.
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf, Section 3; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/Main.lean (declaration OAI.ExactFourier.win_to_fourier)

import Mathlib
import Definitions.Def_ExactFourier
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
open Filter Topology
open CircuitCost

theorem win_to_fourier (win : FiniteWinStatement) : MainStatement := by
  sorry
end ExactFourier

end
end

end OAI
end
