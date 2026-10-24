-- Prove2me | Theorems.Thm_OAI_ExactFourier_SparseReflection_exists_reflection_nnz
-- name    : OAI.ExactFourier.SparseReflection.exists_reflection_nnz
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:04:02.305549+00:00
-- url     : https://prove2.me/theorems/abf6a39c-0e9e-4728-b3ea-420a9c723774
-- title:
--   Sparse reflection: a real symmetric matrix has a reflection R with A(1+R) = 0, 1−R ∈ A·Mat, and price at most (3/4)·nnz(A) + 2|α| (OpenAI exact Fourier circuits)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of `OAI.ExactFourier.main_theorem` (the paper's Theorem 1.1), used in the reflection contradiction that proves the paper's Theorem 8.3 (`OAI.ExactFourier.finite_win`).
--
--   **Notation** (published bundle `Def_ExactFourier` and definitions bundle `OAIQWEXF000` of this split). A matrix is monomial (`IsMonomial`, `MonomialMatrix`) when it is a permutation matrix times an invertible diagonal matrix. A matrix price (`MatrixPrice`) is a function $p$ assigning a real number $p(A)$ to every complex square matrix, indexed by any finite type, such that for invertible matrices: $p(A) \ge 0$ with equality exactly for monomial $A$; $p$ is unchanged by reindexing, by multiplying by monomial matrices on either side, by inversion and by transposition; $p(AB) \le p(A) + p(B)$; $p(A \oplus B) = p(A) + p(B)$; $p(A \otimes B) = |\kappa|\,p(A) + |\iota|\,p(B)$ for $A$ on $\iota$ and $B$ on $\kappa$; and $p$ of the $2 \times 2$ elementary transvection $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ is $1$.
--
--   **The statement.** Let $p$ be a matrix price and $A$ a real symmetric square matrix on a finite linearly ordered type $\alpha$ (every entry equals its complex conjugate), with $\mathrm{nnz}(A)$ nonzero entries. Then there are matrices $R$ and $T$ with
--   $$R^2 = 1,\quad R^{\mathsf T} = R,\quad A(1 + R) = 0,\quad 1 - R = AT,\quad p(R) \le \tfrac34\,\mathrm{nnz}(A) + 2|\alpha|.$$
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf, Section 8; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SparseSpectral.lean (declaration OAI.ExactFourier.SparseReflection.exists_reflection_nnz)

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
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [LinearOrder α]

theorem exists_reflection_nnz (p : MatrixPrice) (A : Matrix α α ℂ) (hA : A.IsSymm)
    (hreal : ∀ i j,star (A i j)=A i j) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧ A*(1+R)=0 ∧ 1-R=A*T ∧
      p.value R≤(3:ℝ)/4*nnz A+2*Fintype.card α := by
  sorry

end ExactFourier.SparseReflection

end
end

end OAI
end
