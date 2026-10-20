-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_matrix_to_body_fin
-- name    : OAI.MetricEntropyDuality.matrix_to_body_fin
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:12:10.678028+00:00
-- url     : https://prove2.me/theorems/df0c5f8b-76cf-4d91-9a77-316550b96e84
-- title:
--   From a separated matrix with a short approximation list to a convex body
-- statement:
--   Let $X,Y$ be finite nonempty sets, $\varepsilon\ge0$, $t>0$. For a matrix $g:Y\times X\to\mathbb R$ with finite $X,Y$, the column combination of $\lambda\in\mathbb R^Y$ is $(g^\top\lambda)(x)=\sum_y\lambda_yg(y,x)$, and a finite list $A$ of functions on $X$ is an $\varepsilon$-approximation if every $g^\top\lambda$ with $\|\lambda\|_1\le1$ is within $\varepsilon$ of some $a\in A$ in the sup norm. Suppose the rows are separated: for $x\ne x'$ some $y$ has $|g(y,x)-g(y,x')|\ge1$. Let $A$ be an $\varepsilon$-approximation and $n=|Y|$. Then there is a symmetric convex body $K\subset\mathbb R^n$ with finite covers in both problems below, such that
--   $$
--   |X|\le N(K,Q_n),\qquad N\bigl(Q_n^\circ,(6\varepsilon+2t)K^\circ\bigr)\le|A| ,
--   $$
--   where $Q_n=[-1,1]^n$ and $Q_n^\circ$ is the $\ell_1$ ball.
--
--   The primal covering number counts rows, while the dual one counts approximants.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/MatrixToBody.lean#L79-L106

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport

open OAI OAI.MetricEntropyDuality
universe uX uY uι
open scoped Pointwise
variable {X : Type uX} {Y : Type uY} [Fintype X] [Fintype Y]

theorem OAI.MetricEntropyDuality.matrix_to_body_fin [Nonempty X] [Nonempty Y]
    (g : Y → X → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t)
    (hsep : ∀ x x', x ≠ x' → ∃ y, 1 ≤ |g y x - g y x'|)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    0 < Fintype.card Y ∧
      ∃ K : Set (RealSpace (Fin (Fintype.card Y))),
        IsSymmetricConvexBody K ∧
        IsSymmetricConvexBody (cube (Fin (Fintype.card Y))) ∧
        Coverable K (cube (Fin (Fintype.card Y))) ∧
        Coverable (polar (cube (Fin (Fintype.card Y)))) ((6 * ε + 2 * t) • polar K) ∧
        Fintype.card X ≤ coveringNumber K (cube (Fin (Fintype.card Y))) ∧
        coveringNumber (polar (cube (Fin (Fintype.card Y))))
          ((6 * ε + 2 * t) • polar K) ≤ A.card := by sorry
