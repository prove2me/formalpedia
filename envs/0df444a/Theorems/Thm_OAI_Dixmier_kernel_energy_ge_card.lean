-- Prove2me | Theorems.Thm_OAI_Dixmier_kernel_energy_ge_card
-- name    : OAI.Dixmier.kernel_energy_ge_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:23:36.011183+00:00
-- url     : https://prove2.me/theorems/e6227dc3-b39b-449e-be64-2a9f9ec7bad8
-- title:
--   A collision kernel of unit rank-one projections has energy at least the number of labels
-- statement:
--   Let $K$ and $I$ be finite sets and $G$ an arbitrary set of labels. Let $(v_i)_{i\in I}$ be unit vectors in $\mathbb{C}^K$ and $s\colon I\to G$ a labelling, which need not be injective. For $g\in G$ form the collision block
--
--   $$W_g=\sum_{i\in I:\ s(i)=g}v_iv_i^*\ \in\mathbb{C}^{K\times K},\qquad (vv^*)_{ab}=v_a\overline{v_b},$$
--
--   and measure it in the unnormalized Hilbert–Schmidt norm $\|W\|_{\mathrm{HS}}^2=\sum_{a,b\in K}|W_{ab}|^2$. Then the total energy of the blocks is at least the number of labels:
--
--   $$|I|\;\le\;\sum_{g\in G}\|W_g\|_{\mathrm{HS}}^2 .$$
--
--   Only the finitely many $g$ in the image $s(I)$ contribute, so the right-hand side is a finite sum. In the construction of uniformly bounded non-unitarizable representations, $W_g$ is the $(1,g)$ block of a translation-invariant operator assembled from unit rank-one projections, and the inequality shows that its energy grows at least like the number of labels; colliding labels $s(i)=s(j)$ do not destroy energy.
--
--   **Formalization Note** The sum over $G$ is a `tsum`; since $W_g=0$ outside the finite image $s(I)$ it is a genuine finite sum. The block $W_g$ is `kernelCoefficients v s g`, a coefficient vector in `EuclideanSpace ℂ (K × K)`. No algebraic structure on $G$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/KernelEnergy.lean#L105-L118

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

theorem OAI.Dixmier.kernel_energy_ge_card (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (s : I → G) : (Fintype.card I : ℝ) ≤ ∑' g, ‖kernelCoefficients v s g‖^2 := by sorry
