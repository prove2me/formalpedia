-- Prove2me | Theorems.Thm_OAI_MetricEntropyDuality_roundWeight_sum_error
-- name    : OAI.MetricEntropyDuality.roundWeight_sum_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T22:33:09.95248+00:00
-- url     : https://prove2.me/theorems/51817691-5818-41c8-87ee-77eb0100b17f
-- title:
--   Error of rounding weights down to a mesh
-- statement:
--   Let $I$ be finite, $\delta>0$, $w_i\ge0$, and $b_i\in[0,1]$. With $\mathrm{round}_\delta(w)=\delta\lfloor w/\delta\rfloor$,
--   $$
--   0\le\sum_iw_ib_i-\sum_i\mathrm{round}_\delta(w_i)\,b_i\le|I|\,\delta .
--   $$
--
--   Rounding every weight down loses at most one mesh step per weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/MetricEntropy/WeightRounding.lean#L98-L117

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
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Definitions.Def_OAI_Analysis_MetricEntropy_LabelEncoding
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionCode
import Definitions.Def_OAI_Analysis_MetricEntropy_WeightRounding

open OAI OAI.MetricEntropyDuality
universe uI
open scoped BigOperators

theorem OAI.MetricEntropyDuality.roundWeight_sum_error {I : Type uI} [Fintype I]
    (δ : ℝ) (hδ : 0 < δ) (w b : I → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    0 ≤ (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i ∧
      (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i ≤
        (Fintype.card I : ℝ) * δ := by sorry
