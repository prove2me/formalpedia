-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_exists_coefficient_representatives
-- name    : OAI.MetricEntropyDuality.exists_coefficient_representatives
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:11:24.423373+00:00
-- url     : https://prove2.me/theorems/9c86ea31-6a4b-4917-b073-814c56034784
-- title:
--   Approximation lists give coefficient centres in the l1 ball
-- statement:
--   Let $\varepsilon\ge0$. For a matrix $g:Y\times X\to\mathbb R$ with finite $X,Y$, the column combination of $\lambda\in\mathbb R^Y$ is $(g^\top\lambda)(x)=\sum_y\lambda_yg(y,x)$, and a finite list $A$ of functions on $X$ is an $\varepsilon$-approximation if every $g^\top\lambda$ with $\|\lambda\|_1\le1$ is within $\varepsilon$ of some $a\in A$ in the sup norm. If $A$ is an $\varepsilon$-approximation, there are centres $c_1,\dots,c_{|A|}$ in the $\ell_1$ ball such that every $\lambda$ with $\|\lambda\|_1\le1$ has some $j$ with
--   $$
--   \|g^\top\lambda-g^\top c_j\|_\infty\le2\varepsilon\quad\text{and}\quad\|\lambda-c_j\|_1\le2 .
--   $$
--
--   The number of centres equals the length of the list and does not depend on the dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/PolarCover.lean#L67-L97

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

open OAI OAI.MetricEntropyDuality
universe uX uY
open scoped BigOperators Pointwise
variable {X : Type uX} {Y : Type uY} [Fintype Y]

theorem OAI.MetricEntropyDuality.exists_coefficient_representatives (g : Y → X → ℝ) (ε : ℝ)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      ∀ lam ∈ l1Ball Y, ∃ j,
        UniformClose (2 * ε) (columnCombination g lam) (columnCombination g (centers j)) ∧
        l1Norm (lam - centers j) ≤ 2 := by sorry
