-- Prove2me | Theorems.Thm_OAI_Dixmier_SignMatrix_frames_for_fintype
-- name    : OAI.Dixmier.SignMatrix.frames_for_fintype
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:23.764932+00:00
-- url     : https://prove2.me/theorems/af8eab56-8070-4152-ae5d-e270934c4d2b
-- title:
--   Unit frames in dimension $\lceil 2r\log(2n)\rceil$ whose subfamilies of size at most $\min(2r,n)$ have synthesis norm at most 10
-- statement:
--   Let $I$ be a finite set with $n=|I|\ge2$ elements and let $r\ge1$ be an integer. Put
--
--   $$k=\big\lceil 2r\log(2n)\big\rceil,\qquad p=\min(2r,n),$$
--
--   where $\log$ is the natural logarithm. Then there are unit vectors $v_i\in\mathbb{C}^k$ ($i\in I$) such that for every subset $J\subseteq I$ with $|J|\le p$ the synthesis operator
--
--   $$T_J\colon\mathbb{C}^J\to\mathbb{C}^k,\qquad T_J\,z=\sum_{i\in J}z_i\,v_i,$$
--
--   has operator norm $\|T_J\|\le10$, both spaces carrying their Euclidean norms. Equivalently, every such subfamily satisfies the Bessel inequality $\sum_{i\in J}|\langle v_i,x\rangle|^2\le100\|x\|^2$ for $x\in\mathbb{C}^k$.
--
--   This is the frame lemma of the construction of uniformly bounded non-unitarizable representations: $n$ unit vectors fit into a space of dimension only $O(r\log n)$ while all their subfamilies of size up to $2r$ stay uniformly bounded. In the application $I$ is the set of $d^\ell$ words of length $\ell$ and $r$ is the endpoint capacity.
--
--   **Formalization Note** The conclusion `FiniteSynthesis.FrameBound v p 10` quantifies over all finite subsets `J` of `I` with at most $p$ elements, including the empty set; $k$ and $p$ are `FrameParameters.dimension n r` and `FrameParameters.subfamilySize n r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Frames.lean#L84-L101

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

theorem OAI.Dixmier.SignMatrix.frames_for_fintype {r : ℕ} (hn : 2 ≤ Fintype.card I) (hr : 1 ≤ r) :
    ∃ v : I → EuclideanSpace ℂ (Fin (FrameParameters.dimension (Fintype.card I) r)),
      (∀ i, ‖v i‖ = 1) ∧
      FiniteSynthesis.FrameBound v (FrameParameters.subfamilySize (Fintype.card I) r) 10 := by sorry
