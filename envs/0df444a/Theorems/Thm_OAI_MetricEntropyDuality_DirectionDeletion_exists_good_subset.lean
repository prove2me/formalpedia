-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_DirectionDeletion_exists_good_subset
-- name    : OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:16:22.368637+00:00
-- url     : https://prove2.me/theorems/546f347b-80da-4274-b44a-527b7dbf42f9
-- title:
--   Deleting the supports of a maximal disjoint family of bad tuples
-- statement:
--   Let $U$ be a finite set, $h\ge1$, $w\in\mathbb N$, and $\mathrm{bad}$ a property of tuples $a:\{1..h\}\to U$ (repetitions allowed). Suppose there are no $w$ bad tuples with pairwise disjoint supports. Then there is $T\subseteq U$ with $|U\setminus T|\le h(w-1)$ such that
--   $$
--   a_1,\dots,a_h\in T\implies a\text{ is not bad}.
--   $$
--
--   Few deletions remove every bad tuple.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/DirectionDeletion.lean#L23-L90

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

open OAI OAI.MetricEntropyDuality
universe uU
open scoped Classical

theorem OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset {U : Type uU} [Fintype U] {h w : ℕ}
    (bad : (Fin h → U) → Prop) (hh : 0 < h)
    (hno : ¬ ∃ L : Fin w → Fin h → U,
      (∀ i, bad (L i)) ∧ DisjointSupports L) :
    ∃ T : Finset U, (Finset.univ \ T).card ≤ h * (w - 1) ∧
      ∀ a : Fin h → U, (∀ j, a j ∈ T) → ¬bad a := by sorry
