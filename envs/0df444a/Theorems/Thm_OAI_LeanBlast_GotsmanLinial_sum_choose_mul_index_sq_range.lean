-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_choose_mul_index_sq_range
-- name    : OAI.LeanBlast.GotsmanLinial.sum_choose_mul_index_sq_range
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:01:32.612733+00:00
-- url     : https://prove2.me/theorems/22e0f15d-6928-4e52-a5cd-59577df6a3d6
-- title:
--   Second raw binomial moment: $\sum_{k}\binom nk k^2=n(n+1)2^n/4$
-- statement:
--   For every natural number $n$, including $n=0$, the binomial coefficients satisfy
--
--   $$
--   \sum_{k=0}^{n}\binom{n}{k}\,k^{2}=\frac{n(n+1)\,2^{n}}{4}.
--   $$
--
--   Both sides are real numbers; for $n=0$ both equal $0$.
--
--   Dividing by $2^n$, the identity says that a binomial random variable $K\sim\mathrm{Bin}(n,\tfrac12)$ has second moment $\mathbb{E}[K^2]=n(n+1)/4$. Together with the row sum $\sum_k\binom nk=2^n$ and the first moment $\sum_k\binom nk k=n2^{n}/2$, it gives the variance $n/4$ of the symmetric binomial distribution. In the Gotsman–Linial argument the binomial coefficients $\binom nk$ are the dimensions of the layers of the degree grading of the Boolean cube, and this moment enters the computation of the centered second moment of that grading.
--
--   **Formalization Note** The sum ranges over $k\in\{0,1,\dots,n\}$ (`Finset.range (n + 1)`), every term is cast to $\mathbb{R}$, and the division by $4$ is real division, so no rounding occurs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BinomialMoments.lean#L52-L72

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators

theorem OAI.LeanBlast.GotsmanLinial.sum_choose_mul_index_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (k : ℝ) ^ 2) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 : ℝ) ^ n / 4 := by sorry
