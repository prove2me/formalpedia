-- Prove2me | Theorems.Thm_OAI_ExactFourier_GraphReflection_lower_bound_blocks
-- name    : OAI.ExactFourier.GraphReflection.lower_bound_blocks
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:03:57.980962+00:00
-- url     : https://prove2.me/theorems/66b96405-8793-485f-a511-1e2d3437ca56
-- title:
--   Graph-reflection lower bound: twice the price of B is at most the price of a compatible symmetric reflection plus 8|α| (OpenAI exact Fourier circuits)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of `OAI.ExactFourier.main_theorem` (the paper's Theorem 1.1), used in the reflection contradiction that proves the paper's Theorem 8.3 (`OAI.ExactFourier.finite_win`).
--
--   **Notation** (published bundle `Def_ExactFourier` and definitions bundle `OAIQWEXF000` of this split). A matrix is monomial (`IsMonomial`, `MonomialMatrix`) when it is a permutation matrix times an invertible diagonal matrix. A matrix price (`MatrixPrice`) is a function $p$ assigning a real number $p(A)$ to every complex square matrix, indexed by any finite type, such that for invertible matrices: $p(A) \ge 0$ with equality exactly for monomial $A$; $p$ is unchanged by reindexing, by multiplying by monomial matrices on either side, by inversion and by transposition; $p(AB) \le p(A) + p(B)$; $p(A \oplus B) = p(A) + p(B)$; $p(A \otimes B) = |\kappa|\,p(A) + |\iota|\,p(B)$ for $A$ on $\iota$ and $B$ on $\kappa$; and $p$ of the $2 \times 2$ elementary transvection $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ is $1$.
--
--   **The statement.** Let $p$ be a matrix price, $B$ an invertible real matrix on a finite type $\alpha$ (every entry equals its complex conjugate), and $\Gamma = \begin{pmatrix} 0 & B \\ B^{-1} & 0\end{pmatrix}$ (`GraphReflection.graph B`). Let $R = \begin{pmatrix} E & F \\ G & H\end{pmatrix}$ be an invertible symmetric matrix on $\alpha \oplus \alpha$ with
--   $$\Gamma(1 + R) = 1 + R \quad\text{and}\quad \Gamma^{\mathsf T}(1 - R) = -(1 - R).$$
--   Then $2\,p(B) \le p(R) + 8\,|\alpha|$.
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf, Section 8; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/GraphBlocks.lean (declaration OAI.ExactFourier.GraphReflection.lower_bound_blocks)

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
namespace ExactFourier.GraphReflection
variable {α : Type} [Fintype α] [DecidableEq α]

theorem lower_bound_blocks (p : MatrixPrice) (B E F G H : Matrix α α ℂ) (hB : IsUnit B)
    (hreal : ∀ i j,star (B i j)=B i j)
    (hR : IsUnit (Matrix.fromBlocks E F G H)) (hs : (Matrix.fromBlocks E F G H).IsSymm)
    (hp : graph B*(1+Matrix.fromBlocks E F G H)=1+Matrix.fromBlocks E F G H)
    (hm : (graph B).transpose*(1-Matrix.fromBlocks E F G H)=-(1-Matrix.fromBlocks E F G H)) :
    2*p.value B≤p.value (Matrix.fromBlocks E F G H)+8*Fintype.card α := by
  sorry

end ExactFourier.GraphReflection

end
end

end OAI
end
