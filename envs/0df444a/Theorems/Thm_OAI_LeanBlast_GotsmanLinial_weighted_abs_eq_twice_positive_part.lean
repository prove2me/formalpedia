-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_weighted_abs_eq_twice_positive_part
-- name    : OAI.LeanBlast.GotsmanLinial.weighted_abs_eq_twice_positive_part
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:40:17.941615+00:00
-- url     : https://prove2.me/theorems/20201dcd-1b42-45df-b577-6f4e1dbc6318
-- title:
--   Mean-zero weighted sums: the absolute first moment is twice the positive-part moment
-- statement:
--   Let $\Omega$ be a finite set, let $w:\Omega\to\mathbb{R}$ be arbitrary real weights, and let $z:\Omega\to\mathbb{R}$ satisfy the mean-zero condition $\sum_{i\in\Omega}w(i)z(i)=0$. Then
--
--   $$
--   \sum_{i\in\Omega}w(i)\,|z(i)|=2\sum_{i\in\Omega}w(i)\max\bigl(z(i),0\bigr).
--   $$
--
--   No sign condition or normalization is imposed on the weights. For a probability weight this is the familiar fact that a mean-zero random variable $Z$ satisfies $\mathbb{E}|Z|=2\,\mathbb{E}[Z^+]$, where $Z^+=\max(Z,0)$. In the finite one-sided coupling lemma it is applied to the increment of a monotone potential between two identically distributed variables: that increment has mean zero, so its absolute first moment is controlled by its positive part alone, which is where the one-sided step bound enters.
--
--   **Formalization Note** The statement holds for any `Fintype` $\Omega$ and any real-valued $w$; the maximum is the real `max (z i) 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean#L44-L62

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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements

open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω]

theorem OAI.LeanBlast.GotsmanLinial.weighted_abs_eq_twice_positive_part (w z : Ω → ℝ)
    (hzero : ∑ i, w i * z i = 0) :
    ∑ i, w i * |z i| = 2 * ∑ i, w i * max (z i) 0 := by sorry
