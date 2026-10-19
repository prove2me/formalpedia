-- Prove2me | Theorems.Thm_OAI_NCHitting_exists_nonzero_divisible_minor
-- name    : OAI.NCHitting.exists_nonzero_divisible_minor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:09:55.537844+00:00
-- url     : https://prove2.me/theorems/2fa1423f-6c57-4334-9322-0d96bf3d5941
-- title:
--   A maximal minor of $Z$ is nonzero and divisible by $\det W$ when $ZG=DH$, $H=WC$ and $W=HE$
-- statement:
--   Let $R$ be an integral domain and $K,I$ finite index sets with decidable equality. Consider matrices
--   $$
--   Z,H,C\in R^{K\times I},\qquad G\in R^{I\times I},\qquad D,W\in R^{K\times K},\qquad E\in R^{I\times K},
--   $$
--   with $G$ invertible, $\det D\ne0$, $\det W\ne0$, and
--   $$
--   ZG=DH,\qquad H=WC,\qquad W=HE.
--   $$
--   Then there is a map $f:K\to I$ such that the square submatrix $Z_f=(Z_{k,f(k')})_{k,k'\in K}$ (columns of $Z$ selected by $f$) satisfies
--   $$
--   \det Z_f\ne0\qquad\text{and}\qquad \det W\ \big|\ \det Z_f .
--   $$
--
--   In the application, $W$ is a Wronskian of power series, $H$ is a matrix of derivatives, $D$ is a diagonal matrix of powers of a denominator, and $Z$ is a matrix of polynomials. The lemma produces a nonzero polynomial minor that the Wronskian divides.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/MinorFactor.lean#L15-L38

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

open OAI OAI.NCHitting
open Matrix
variable {R : Type*} [CommRing R] [IsDomain R]
variable {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

theorem OAI.NCHitting.exists_nonzero_divisible_minor
    (Z H : Matrix K I R) (G : Matrix I I R) (D W : Matrix K K R)
    (C : Matrix K I R) (E : Matrix I K R)
    (hG : IsUnit G) (hD : D.det ≠ 0) (hW : W.det ≠ 0)
    (hZG : Z * G = D * H) (hHC : H = W * C) (hHE : W = H * E) :
    ∃ f : K → I, (Z.submatrix id f).det ≠ 0 ∧ W.det ∣ (Z.submatrix id f).det := by sorry
