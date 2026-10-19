-- Prove2me | Theorems.Thm_OAI_NCHitting_coeff_J
-- name    : OAI.NCHitting.coeff_J
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:13:14.593984+00:00
-- url     : https://prove2.me/theorems/ec0485b9-e52a-45ec-9a8d-8ea9e81153a6
-- title:
--   Coefficients of the integral of $a/(X+i)$
-- statement:
--   Let $F$ be a field and $i,r\in\mathbb{N}$. For $a\in F[[X]]$, let
--   $$
--   J_i(a)=\int_0^X a\,\kappa_i,\qquad \kappa_i=\sum_{t\ge0}\frac{(-1)^t}{i^{\,t+1}}X^t ,
--   $$
--   where the formal integral is $\int\sum_ta_tX^t=\sum_ta_t\frac{X^{t+1}}{t+1}$ and $\kappa_i$ expands $1/(X+i)$ for $i\ge1$. Then
--   $$
--   [X^r]\,J_i(a)=\sum_{q=0}^{r-1}\frac{(-1)^{r-q-1}}{r\,i^{\,r-q}}\,[X^q]\,a .
--   $$
--
--   So $J_i$ acts on coefficient vectors through an explicit strictly lower-triangular matrix with rational entries. This matrix is the generator matrix substituted for the variables in the hitting set.
--
--   **Formalization Note** The identity holds over any field with Lean's convention $x/0=0$. For $r=0$ the sum is empty and both sides are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Series.lean#L107-L123

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
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series

open OAI OAI.NCHitting
open PowerSeries
variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem OAI.NCHitting.coeff_J (i r : ℕ) (a : PowerSeries F) :
    PowerSeries.coeff r (J i a) =
      ∑ q ∈ Finset.range r,
        ((-1 : F)^(r-q-1) / ((r : F) * (i : F)^(r-q))) * PowerSeries.coeff q a := by sorry
