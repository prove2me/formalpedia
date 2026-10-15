-- Prove2me | Theorems.Thm_OAI_LeanBlast_GotsmanLinial_weighted_abs_le_of_second_moment
-- name    : OAI.LeanBlast.GotsmanLinial.weighted_abs_le_of_second_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T03:38:18.564112+00:00
-- url     : https://prove2.me/theorems/a7795635-f9e4-4029-9a2b-fa325d4e1474
-- title:
--   Weighted Cauchy–Schwarz: a second-moment bound controls the first absolute moment
-- statement:
--   Let $\Omega$ be a finite set and let $w:\Omega\to\mathbb{R}$ be a probability weight, meaning $w(i)\ge 0$ for every $i\in\Omega$ and $\sum_{i\in\Omega}w(i)=1$ (zero weights are allowed). Let $f:\Omega\to\mathbb{R}$ be any function and let $\sigma\ge0$ be a real number with $\sum_{i\in\Omega}w(i)f(i)^2\le\sigma^2$. Then
--
--   $$
--   \sum_{i\in\Omega}w(i)\,|f(i)|\le\sigma .
--   $$
--
--   In probabilistic language: if a random variable $X$ taking finitely many values satisfies $\mathbb{E}[X^2]\le\sigma^2$, then $\mathbb{E}|X|\le\sigma$. This elementary estimate is used in the finite one-sided coupling lemma to bound the mean absolute deviation $\mathbb{E}|U-m|$ of a variable from a center $m$ by the square root of its second moment about $m$.
--
--   **Formalization Note** $\Omega$ is any `Fintype`; the weights are an arbitrary real function constrained only by the stated hypotheses, and no measure-theoretic structure is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/FiniteCoupling.lean#L22-L42

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

theorem OAI.LeanBlast.GotsmanLinial.weighted_abs_le_of_second_moment (w f : Ω → ℝ) (σ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hσ : 0 ≤ σ)
    (hsecond : ∑ i, w i * (f i) ^ 2 ≤ σ ^ 2) :
    ∑ i, w i * |f i| ≤ σ := by sorry
