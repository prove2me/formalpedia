-- Prove2me | Theorems.Thm_OAI_NCHitting_scaled_derivative_row
-- name    : OAI.NCHitting.scaled_derivative_row
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:07:30.64099+00:00
-- url     : https://prove2.me/theorems/c0e779cd-e799-4eb6-a2ff-ba7767a2ac0c
-- title:
--   Cleared derivatives of an output row of a system $qG'=PG$ are polynomial combinations of $G$
-- statement:
--   Let $F$ be a field and $I$ a finite index set. Let $q\in F[X]$, $P\in F[X]^{I\times I}$, $u\in F^I$, and let $G\in F[[X]]^{I\times I}$ be a matrix of power series satisfying the linear differential system
--   $$
--   q\,G_{tl}'=\sum_{a\in I}P_{ta}\,G_{al}\qquad\text{for all } t,l\in I,
--   $$
--   where polynomials are viewed as power series. Let $N_j(t)$ be the numerator rows: $N_0(t)=u_t$ and $N_{j+1}(t)=qN_j(t)'-j\,q'N_j(t)+\sum_sN_j(s)P_{st}$. Then for every $j\in\mathbb{N}$ and $l\in I$,
--   $$
--   q^j\,D^j\Bigl(\sum_{t\in I}u_t\,G_{tl}\Bigr)=\sum_{t\in I}N_j(t)\,G_{tl},
--   $$
--   where $D^j$ is the $j$-th formal derivative.
--
--   After clearing the denominator $q^j$, every derivative of a linear combination of the entries of a column of $G$ is again such a combination, with explicit polynomial coefficients. This is the step that turns analytic information (vanishing of many derivatives) into polynomial identities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/ScaledDerivatives.lean#L67-L91

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

open OAI OAI.NCHitting
open PowerSeries Polynomial Matrix
variable {F : Type*} [Field F]
variable {I : Type*} [Fintype I]

theorem OAI.NCHitting.scaled_derivative_row (q : F[X]) (P : Matrix I I F[X]) (u : I → F)
    (G : Matrix I I (PowerSeries F))
    (hG : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (j : ℕ) (l : I) :
    (q : PowerSeries F)^j * derivativeIter j
        (∑ t : I, PowerSeries.C (u t) * G t l) =
      ∑ t : I, (numeratorRow q P u j t : PowerSeries F) * G t l := by sorry
