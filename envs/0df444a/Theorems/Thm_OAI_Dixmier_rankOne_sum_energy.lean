-- Prove2me | Theorems.Thm_OAI_Dixmier_rankOne_sum_energy
-- name    : OAI.Dixmier.rankOne_sum_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:23:21.17037+00:00
-- url     : https://prove2.me/theorems/51cb54d6-9921-481e-b9c4-f1bd60a69020
-- title:
--   Sums of unit rank-one projections have Hilbert–Schmidt energy at least the number of summands
-- statement:
--   Let $K$ be a finite index set. Identify $K\times K$ complex matrices with vectors in $\mathbb{C}^{K\times K}$ and equip them with the unnormalized Hilbert–Schmidt (Frobenius) norm $\|W\|_{\mathrm{HS}}^2=\sum_{a,b\in K}|W_{ab}|^2$. For $v\in\mathbb{C}^K$ let $vv^*$ denote the rank-one matrix with entries $(vv^*)_{ab}=v_a\overline{v_b}$.
--
--   Let $(v_i)_{i\in I}$ be a family of unit vectors in $\mathbb{C}^K$ indexed by an arbitrary set $I$. Then for every finite subset $J\subseteq I$,
--
--   $$|J|\;\le\;\Big\|\sum_{i\in J}v_iv_i^*\Big\|_{\mathrm{HS}}^2 .$$
--
--   The inequality reflects the fact that the Hilbert–Schmidt inner products $\langle v_jv_j^*,v_iv_i^*\rangle_{\mathrm{HS}}=|\langle v_i,v_j\rangle|^2$ are all nonnegative, so adding unit rank-one projections never cancels energy, even when vectors repeat. It is the fibrewise estimate behind the lower bound for the energy of collision kernels built from such projections.
--
--   **Formalization Note** A matrix is represented by its coefficient vector in `EuclideanSpace ℂ (K × K)`, whose Euclidean norm is the Hilbert–Schmidt norm above; $vv^*$ is `rankOneCoefficients v`. The index type $I$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/KernelEnergy.lean#L55-L74

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy

open OAI OAI.Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

omit [Fintype I] in
theorem OAI.Dixmier.rankOne_sum_energy (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (J : Finset I) : (J.card : ℝ) ≤ ‖∑ i ∈ J, rankOneCoefficients (v i)‖^2 := by sorry
