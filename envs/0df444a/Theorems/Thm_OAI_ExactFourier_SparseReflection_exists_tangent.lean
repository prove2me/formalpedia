-- Prove2me | Theorems.Thm_OAI_ExactFourier_SparseReflection_exists_tangent
-- name    : OAI.ExactFourier.SparseReflection.exists_tangent
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:03:37.213475+00:00
-- url     : https://prove2.me/theorems/dd93a583-ea85-43cc-a923-cfba7be8db0b
-- title:
--   Tangent family: a diagonal plus a list of pair terms is the derivative at 0 of invertible matrices of price at most (3/2)·(list length) (OpenAI exact Fourier circuits)
-- statement:
--   An intermediate statement of the split of OpenAI's proof of `OAI.ExactFourier.main_theorem` (the paper's Theorem 1.1), used in the reflection contradiction that proves the paper's Theorem 8.3 (`OAI.ExactFourier.finite_win`).
--
--   **Notation** (published bundle `Def_ExactFourier` and definitions bundle `OAIQWEXF000` of this split). A matrix is monomial (`IsMonomial`, `MonomialMatrix`) when it is a permutation matrix times an invertible diagonal matrix. A matrix price (`MatrixPrice`) is a function $p$ assigning a real number $p(A)$ to every complex square matrix, indexed by any finite type, such that for invertible matrices: $p(A) \ge 0$ with equality exactly for monomial $A$; $p$ is unchanged by reindexing, by multiplying by monomial matrices on either side, by inversion and by transposition; $p(AB) \le p(A) + p(B)$; $p(A \oplus B) = p(A) + p(B)$; $p(A \otimes B) = |\kappa|\,p(A) + |\iota|\,p(B)$ for $A$ on $\iota$ and $B$ on $\kappa$; and $p$ of the $2 \times 2$ elementary transvection $\begin{pmatrix} 1 & 0 \\ 1 & 1\end{pmatrix}$ is $1$.
--
--   **Further notation.** A pair term (`PairTerm`) on $\alpha$ is $(i, j, a, b)$ with $i \neq j$ and $a, b \neq 0$; its direction is the matrix $a\,e_{ij} + b\,e_{ji}$.
--
--   **The statement.** Let $p$ be a matrix price, $d : \alpha \to \mathbb C$ and $L$ a list of pair terms on a finite type $\alpha$. Then there are a matrix $Q(s)$ of complex polynomials and a finite exceptional set $E \subseteq \mathbb C$ such that
--   $$Q(0) = \mathrm{diag}(d) + \sum_{u \in L} \mathrm{direction}(u),$$
--   and for every $s \notin E$ the matrix $1 + s\,Q(s)$ is invertible with $p(1 + s\,Q(s)) \le \tfrac32\,|L|$.
-- source:
--   OpenAI, Finite tensor savings and exact Fourier circuits, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 130; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf, Section 8; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/FourierCircuit/SymmetricLaplacian.lean (declaration OAI.ExactFourier.SparseReflection.exists_tangent)

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
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_tangent (p : MatrixPrice) (d : α → ℂ) (L : List (PairTerm α)) :
    ∃ Q : Matrix α α (Polynomial ℂ),∃ E : Finset ℂ,
      Q.map (evalRingHom 0)=Matrix.diagonal d+(L.map PairTerm.direction).sum ∧
      ∀ s : ℂ,s∉E → IsUnit (1+s•Q.map (evalRingHom s)) ∧
        p.value (1+s•Q.map (evalRingHom s))≤(3:ℝ)/2*L.length := by
  sorry

end ExactFourier.SparseReflection

end
end

end OAI
end
