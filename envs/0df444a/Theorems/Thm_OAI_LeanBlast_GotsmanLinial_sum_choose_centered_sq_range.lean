-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_sum_choose_centered_sq_range
-- name    : OAI.LeanBlast.GotsmanLinial.sum_choose_centered_sq_range
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:03:59.695529+00:00
-- url     : https://prove2.me/theorems/e2f11319-a27a-4904-aff5-efdde3481318
-- title:
--   Centered second binomial moment: $\sum_{k}\binom nk (k-n/2)^2=n2^n/4$
-- statement:
--   For every natural number $n$, including $n=0$,
--
--   $$
--   \sum_{k=0}^{n}\binom{n}{k}\Bigl(k-\frac n2\Bigr)^{2}=\frac{n\,2^{n}}{4},
--   $$
--
--   where $n/2$ is the real number $n/2$ (not an integer quotient) and all quantities are real.
--
--   After division by $2^n$ this says that the symmetric binomial distribution $\mathrm{Bin}(n,\tfrac12)$, whose mean is $n/2$, has variance $n/4$. In the Gotsman–Linial argument the layers of the degree grading of the Boolean cube have dimensions $\binom nk$, so this sum is the squared Hilbert–Schmidt norm of the centered grading $\sum_k (k-\tfrac n2)P_k$; it supplies the variance $n/4$ from which the factor $\sqrt n$ of the final bound arises.
--
--   **Formalization Note** The sum is over `Finset.range (n + 1)`, with every term cast to $\mathbb{R}$; the identity is stated before normalization by $2^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/BinomialMoments.lean#L74-L90

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

theorem OAI.LeanBlast.GotsmanLinial.sum_choose_centered_sq_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ((k : ℝ) - (n : ℝ) / 2) ^ 2) =
      (n : ℝ) * (2 : ℝ) ^ n / 4 := by sorry
