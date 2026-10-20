-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_exists_profile_pivots
-- name    : OAI.MetricEntropyDuality.exists_profile_pivots
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:28:50.152564+00:00
-- url     : https://prove2.me/theorems/ee708796-567f-4fa7-a968-c62ba2227bd3
-- title:
--   A common index and greedy pivots at every level
-- statement:
--   Let $L_i:X\to\Lambda_i$ be label maps and, for a set $T$ of indices, let $d_T$ be the extended distance of the partition graph in which distinct $x,y$ are adjacent when $L_i(x)=L_i(y)$ for some $i\in T$. Columns $y$ have centres $v_y\in X$, label sets $T_y$ and weights $\mu_y\ge0$. Assume $\sum_y\mu_y\le1$, $u\ge1$, $\theta>0$, $s\theta\ge1$, and $|\{1..u\}\setminus T_y|\le\theta u$ for all $y$. Then for every $h$ there are an index $i$, pivot centres $c_{j,k}$ and assignments $\alpha_j$ ($j<h$, $k\le s$) such that the columns omitting $i$ have mass at most $\theta$. Moreover $\alpha_j(y)=k$ implies $i\in T_y$ and $d_{T_y}(c_{j,k},v_y)\le j$, and for every level $j$ and point $x$,
--   $$
--   \sum_{y:\ i\in T_y,\ d_{T_y}(x,v_y)\le j,\ \alpha_j(y)=\mathrm{none}}\mu_y\le\theta .
--   $$
--
--   One index is chosen once; the pivots depend on the level.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/ProfilePivots.lean#L24-L57

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
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots

open OAI OAI.MetricEntropyDuality
universe uX uY uLabel
open scoped BigOperators Classical

theorem OAI.MetricEntropyDuality.exists_profile_pivots {X : Type uX} {Y : Type uY}
    [Fintype X] [Nonempty X] [Fintype Y]
    {u : ℕ} {Label : Fin u → Type uLabel}
    (L : (i : Fin u) → X → Label i) (v : Y → X) (T : Y → Finset (Fin u))
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (hu : 0 < u) (θ : ℝ) (hθ : 0 < θ) (s : ℕ) (hs : 1 ≤ (s : ℝ) * θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) (h : ℕ) :
    ∃ i : Fin u, ∃ centers : Fin h → Fin s → X,
      ∃ assigned : Fin h → Y → Option (Fin s),
        (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ ∧
        (∀ j y k, assigned j y = some k →
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val (centers j k) (v y)) ∧
        (∀ j x, (∑ y ∈ Finset.univ.filter (fun y =>
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y) ∧
            assigned j y = none), μ y) ≤ θ) := by sorry
