-- Prove2me | Theorems.Thm_OAI_Dixmier_SignMatrix_exists_sign_matrix
-- name    : OAI.Dixmier.SignMatrix.exists_sign_matrix
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:25:44.236244+00:00
-- url     : https://prove2.me/theorems/946b9260-1d5d-4097-b2ac-312b4c0e6dae
-- title:
--   A sign matrix all of whose $p$-column synthesis operators have norm at most 10
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$. Let $n,k,p$ be natural numbers with $k\ge1$ and
--
--   $$2\,n^{p}\,9^{k+p}\,e^{-25k/2}<1 .$$
--
--   For a sign matrix $\sigma\colon[k]\times[n]\to\{-1,+1\}$ let $v^\sigma_i\in\mathbb{R}^k$ ($i\in[n]$) be its normalized columns, $(v^\sigma_i)_a=\sigma(a,i)/\sqrt k$, and for an injective map $e\colon[p]\to[n]$ let
--
--   $$A_{\sigma,e}\colon\mathbb{R}^p\to\mathbb{R}^k,\qquad A_{\sigma,e}\,z=\sum_{j\in[p]}z_j\,v^\sigma_{e(j)},$$
--
--   be the synthesis operator of the selected columns, where $\mathbb{R}^p$ and $\mathbb{R}^k$ carry the Euclidean norm. Then there is a single sign matrix $\sigma$ such that
--
--   $$\|A_{\sigma,e}\|\le10\qquad\text{for every injective }e\colon[p]\to[n].$$
--
--   This is the probabilistic core of the frame construction: $n$ normalized random sign vectors in dimension $k$, which may be much smaller than $n$, can be chosen so that every ordered selection of $p$ of them has synthesis operator of norm at most $10$.
--
--   **Formalization Note** Signs are Booleans, with `true` read as $+1$ and `false` as $-1$ (`FiniteSigns.sign`); the operator is `synthesis σ e` and injective maps are embeddings of `Fin p` into `Fin n`. If $p>n$ there are no such embeddings and the conclusion is vacuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FrameSelection.lean#L18-L87

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
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters

open OAI OAI.Dixmier OAI.Dixmier.SignMatrix
open Finset

theorem OAI.Dixmier.SignMatrix.exists_sign_matrix {n k p : ℕ} (hk : 0 < k)
    (hf : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1) :
    ∃ σ : Fin k × Fin n → Bool, ∀ e : Fin p ↪ Fin n, ‖synthesis σ e‖ ≤ 10 := by sorry
