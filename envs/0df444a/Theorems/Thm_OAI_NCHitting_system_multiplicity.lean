-- Prove2me | Theorems.Thm_OAI_NCHitting_system_multiplicity
-- name    : OAI.NCHitting.system_multiplicity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:10:19.943647+00:00
-- url     : https://prove2.me/theorems/f8c00daf-d38a-47db-b89b-1578c971048e
-- title:
--   Multiplicity bound $(n-1)\binom{m}{2}+m$ for outputs of a rational linear differential system
-- statement:
--   Let $F$ be a field of characteristic zero, $I$ a finite index set with $m=|I|$ elements, and $n\ge1$. Let $q\in F[X]$ be a nonzero polynomial with $\deg q\le n$, and let $P=(P_{tl})$ be an $I\times I$ matrix of polynomials with $\deg P_{tl}\le n-1$. Let $G\in F[[X]]^{I\times I}$ be an invertible matrix of power series solving
--   $$
--   q\,G_{tl}'=\sum_{a\in I}P_{ta}\,G_{al}\qquad(t,l\in I).
--   $$
--   For $u,v\in F^I$ let $y=u^{\mathsf T}Gv=\sum_l\bigl(\sum_tu_tG_{tl}\bigr)v_l$. If $y\ne0$, then
--   $$
--   \operatorname{ord}y<(n-1)\binom{m}{2}+m .
--   $$
--
--   A nonzero output of an $m$-dimensional linear differential system with polynomial coefficients of degree below $n$ therefore vanishes at the origin to bounded order. This multiplicity estimate is what makes a polynomial-size jet detect nonzero series.
--
--   **Formalization Note** $\operatorname{ord}y$ is `order.toNat`, $m$ is `Fintype.card I`, and polynomials are coerced into power series. Invertibility of $G$ is `IsUnit G` in the matrix ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Multiplicity.lean#L57-L170

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity

open OAI OAI.NCHitting
open PowerSeries Polynomial Matrix Submodule
variable {F : Type*} [Field F] [CharZero F]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem OAI.NCHitting.system_multiplicity (n : ℕ) (hn : 0 < n)
    (q : F[X]) (P : Matrix I I F[X]) (u v : I → F)
    (G : Matrix I I (PowerSeries F))
    (hq : q.natDegree ≤ n) (hqn : q ≠ 0)
    (hP : ∀ t l, (P t l).natDegree ≤ n-1) (hG : IsUnit G)
    (hD : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (hy : systemScalarOutput u v G ≠ 0) :
    (systemScalarOutput u v G).order.toNat <
      (n-1) * (Fintype.card I).choose 2 + Fintype.card I := by sorry
