-- Prove2me | Theorems.Thm_OAI_PermanentBorder_SliceParameters_monomial_mem_of_variable_powers
-- name    : OAI.PermanentBorder.SliceParameters.monomial_mem_of_variable_powers
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:55:38.749477+00:00
-- url     : https://prove2.me/theorems/2b3ec595-c42e-4c7b-ab26-411773387df6
-- title:
--   Monomials of large degree lie in any ideal containing a power of every variable
-- statement:
--   Let $K$ be a commutative semiring, $\sigma$ a finite set of variables and $I$ an ideal of the polynomial ring $K[X_j : j\in\sigma]$. Suppose that every variable has a power in $I$, that is, there are $N_j\in\mathbb{N}$ with $X_j^{N_j}\in I$ for all $j\in\sigma$. For an exponent vector $s\in\mathbb{N}^\sigma$ write $|s|=\sum_{j\in\sigma}s_j$ and $X^s=\prod_{j\in\sigma}X_j^{s_j}$. Then for every exponent vector $s$ and every coefficient $c\in K$,
--   $$
--   |s|>\sum_{j\in\sigma}N_j\quad\Longrightarrow\quad c\,X^s\in I .
--   $$
--
--   This is the combinatorial half of the fact that an ideal containing a power of every variable contains every polynomial whose monomials all have large enough degree. Combined with the Nullstellensatz, it turns the geometric condition "the only common zero is the origin" into an explicit degree beyond which all homogeneous polynomials lie in the ideal.
--
--   **Formalization Note** Exponent vectors are finitely supported functions `σ →₀ ℕ`, $|s|$ is `s.degree`, and $c\,X^s$ is `monomial s c`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SmoothSlices.lean#L195-L211

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices

open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial

theorem OAI.PermanentBorder.SliceParameters.monomial_mem_of_variable_powers {K σ : Type*} [CommSemiring K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (N : σ → ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K)^(N j) ∈ I)
    (s : σ →₀ ℕ) (c : K) (hs : (∑ j, N j) < s.degree) : monomial s c ∈ I := by sorry
