-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_FiniteProductCounting_prob_allEvents_eq_prod
-- name    : OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:15:26.486232+00:00
-- url     : https://prove2.me/theorems/58a17281-aa00-4f5e-a87e-3f2a1c815750
-- title:
--   Product formula for events on pairwise disjoint coordinates
-- statement:
--   For finite sets $U$ and $E\ne\varnothing$, the sample space is $E^U$ with uniform probability $\Pr(A)=|A|/|E|^{|U|}$; an event $A$ depends only on $S\subseteq U$ if samples agreeing on $S$ are both in $A$ or both outside it. Let $(A_j)_{j\in s}$ be events where $A_j$ depends only on $S_j$, with the sets $S_j$ pairwise disjoint for $j\in s$. Then
--   $$
--   \Pr\Bigl(\bigcap_{j\in s}A_j\Bigr)=\prod_{j\in s}\Pr(A_j) .
--   $$
--
--   Finitely many events on disjoint coordinate sets are mutually independent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/FiniteProductCounting.lean#L155-L176

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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.FiniteProductCounting
universe uU uE uJ
open scoped BigOperators
variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]
variable [Nonempty E]

theorem OAI.MetricEntropyDuality.FiniteProductCounting.prob_allEvents_eq_prod {J : Type uJ} [DecidableEq J]
    (s : Finset J) (S : J → Finset U) (A : J → Finset (U → E))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    prob (allEvents s A) = ∏ j ∈ s, prob (A j) := by sorry
