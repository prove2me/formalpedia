-- Prove2me | Theorems.Thm_OAI_NCHitting_numeratorRow_degree
-- name    : OAI.NCHitting.numeratorRow_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:07:10.415289+00:00
-- url     : https://prove2.me/theorems/7230fd92-7941-4632-ad53-93a0540513b9
-- title:
--   Degree bound $j(n-1)$ for the numerator rows of a rational linear system
-- statement:
--   Let $F$ be a field, $I$ a finite index set, and $n\ge1$. Let $q\in F[X]$ with $\deg q\le n$, let $P=(P_{tl})_{t,l\in I}$ be polynomials with $\deg P_{tl}\le n-1$, and let $u\in F^I$. Define polynomials $N_j(l)$ by $N_0(l)=u_l$ and
--   $$
--   N_{j+1}(l)=q\,N_j(l)'-j\,q'\,N_j(l)+\sum_{t\in I}N_j(t)\,P_{tl}.
--   $$
--   Then for every $j\in\mathbb{N}$ and $l\in I$,
--   $$
--   \deg N_j(l)\le j\,(n-1).
--   $$
--
--   The numerators produced by repeated differentiation of a system $qG'=PG$ therefore grow in degree by at most $n-1$ per derivative. This controls the degree of determinants built from them.
--
--   **Formalization Note** Degrees are `natDegree`, so the zero polynomial has degree $0$; $n-1$ is natural-number subtraction, which is harmless since $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/NumeratorRows.lean#L34-L63

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
open Polynomial
variable {F : Type*} [Field F]

theorem OAI.NCHitting.numeratorRow_degree {I : Type*} [Fintype I] {n : ℕ} (hn : 0 < n)
    (q : F[X]) (P : Matrix I I F[X]) (u : I → F)
    (hq : q.natDegree ≤ n) (hP : ∀ t l, (P t l).natDegree ≤ n-1)
    (j : ℕ) (l : I) :
    (numeratorRow q P u j l).natDegree ≤ j * (n-1) := by sorry
