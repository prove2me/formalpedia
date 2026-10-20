-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_CompressionLevels_ballIndicator_le_assignedIndicator_add
-- name    : OAI.MetricEntropyDuality.CompressionLevels.ballIndicator_le_assignedIndicator_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:29:18.661378+00:00
-- url     : https://prove2.me/theorems/eb67557b-0e7d-4d2e-b981-68b1308c4e4e
-- title:
--   Pointwise comparison of a ball indicator with its assigned replacement
-- statement:
--   Let $L_i:X\to\Lambda_i$ be label maps and, for a set $T$ of indices, let $d_T$ be the extended distance of the partition graph in which distinct $x,y$ are adjacent when $L_i(x)=L_i(y)$ for some $i\in T$. Columns $y$ have centres $v_y\in X$, label sets $T_y$ and weights $\mu_y\ge0$. Let $i$ be an index, $c_k$ pivot centres and $\mathrm{rep}_k$ replacement pivots with $L_i(\mathrm{rep}_k)=L_i(c_k)$, and let an optional assignment send column $y$ to a slot $k$ only if $i\in T_y$ and $d_{T_y}(c_k,v_y)\le j$. The assigned indicator of $y$ is $0$ if $y$ is unassigned and $\mathbf 1[d_{T_y}(x,\mathrm{rep}_k)\le2j+1]$ if $y$ is assigned to $k$. Then for every point $x$ and column $y$,
--   $$
--   \mathbf 1[d_{T_y}(x,v_y)\le j]\le\mathrm{assigned}_y(x)+\mathbf 1[i\notin T_y]+\mathbf 1[i\in T_y,\ d_{T_y}(x,v_y)\le j,\ y\text{ unassigned}] .
--   $$
--
--   Loss can only come from columns omitting the common index or left unassigned.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/CompressionLevels.lean#L56-L82

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
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.CompressionLevels
universe uX uY uK uι uLabel
open scoped BigOperators Classical
variable {X : Type uX} {Y : Type uY} {K : Type uK} {ι : Type uι} {Label : ι → Type uLabel}

theorem OAI.MetricEntropyDuality.CompressionLevels.ballIndicator_le_assignedIndicator_add
    (L : (i : ι) → X → Label i) (v : Y → X) (T : Y → Finset ι)
    (i : ι) (j : ℕ) (centers rep : K → X) (assignment : Y → Option K)
    (hassign : ∀ y k, assignment y = some k →
      i ∈ T y ∧ PartitionGraph.near L (T y) j (centers k) (v y))
    (hrep : ∀ k, L i (rep k) = L i (centers k)) (x : X) (y : Y) :
    ballIndicator L (T y) j x (v y) ≤
      assignedIndicator L T rep assignment j x y +
        (if i ∉ T y then 1 else 0) +
        (if i ∈ T y ∧ PartitionGraph.near L (T y) j x (v y) ∧
          assignment y = none then 1 else 0) := by sorry
