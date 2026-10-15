-- Prove2me | Theorems.Thm_OAI_Dixmier_SignMatrix_all_subfamilies
-- name    : OAI.Dixmier.SignMatrix.all_subfamilies
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:06.032774+00:00
-- url     : https://prove2.me/theorems/58d995eb-a956-4d74-91fe-7de8c8d20984
-- title:
--   Norm bounds for $p$-selections of real sign vectors extend to all complex subfamilies of size at most $p$
-- statement:
--   Write $[m]=\{0,1,\dots,m-1\}$. Let $I$ be a finite set, let $k,p$ be natural numbers with $p\le|I|$, and let $\sigma\colon[k]\times I\to\{-1,+1\}$ be a sign matrix with normalized columns $v_i\in\mathbb{R}^k$, $(v_i)_a=\sigma(a,i)/\sqrt k$. Assume that for every injective map $e\colon[p]\to I$ the real synthesis operator
--
--   $$A_e\colon\mathbb{R}^p\to\mathbb{R}^k,\qquad A_e\,z=\sum_{j\in[p]}z_j\,v_{e(j)},$$
--
--   satisfies $\|A_e\|\le10$. Then for every subset $J\subseteq I$ with $|J|\le p$, the complex synthesis operator
--
--   $$T_J\colon\mathbb{C}^J\to\mathbb{C}^k,\qquad T_J\,z=\sum_{i\in J}z_i\,v_i,$$
--
--   in which each real vector $v_i$ is regarded as a vector of $\mathbb{C}^k$, satisfies $\|T_J\|\le10$. All spaces carry their Euclidean norms.
--
--   This upgrades a bound for ordered selections of exactly $p$ real columns to the form needed for the frame lemma: all subfamilies of size at most $p$ (including the empty one), with complex coefficients.
--
--   **Formalization Note** $[k]$ and $[p]$ are `Fin k` and `Fin p`; signs are Booleans with `true` read as $+1$ and `false` as $-1$. The real operator is `synthesis σ e`, the complex one is `FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Frames.lean#L41-L68

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
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames

open OAI OAI.Dixmier OAI.Dixmier.SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
private noncomputable local instance instDecidableEq_oAI_3 : DecidableEq I := Classical.decEq I
private noncomputable local instance instDecidableEq_oAI_4 : DecidableEq J := Classical.decEq J
private noncomputable local instance instDecidableEq_oAI_5 : DecidableEq L := Classical.decEq L
private noncomputable local instance instDecidableEq_oAI_6 : DecidableEq K := Classical.decEq K

theorem OAI.Dixmier.SignMatrix.all_subfamilies {k p : ℕ} (hp : p ≤ Fintype.card I) (σ : Fin k × I → Bool)
    (hσ : ∀ e : Fin p ↪ I, ‖synthesis σ e‖ ≤ 10) :
    ∀ J : Finset I, J.card ≤ p →
      ‖FiniteSynthesis.synthesis (fun i => ComplexFrames.ofReal (vector σ i)) J‖ ≤ 10 := by sorry
