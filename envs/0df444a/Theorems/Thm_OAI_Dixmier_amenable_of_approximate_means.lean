-- Prove2me | Theorems.Thm_OAI_Dixmier_amenable_of_approximate_means
-- name    : OAI.Dixmier.amenable_of_approximate_means
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:45.860904+00:00
-- url     : https://prove2.me/theorems/3e75a6ca-0007-424d-990c-d89cb13e0cee
-- title:
--   Approximately invariant positive normalized means yield an invariant mean by weak-star compactness
-- statement:
--   Let $G$ be a group with the discrete topology, and let $\ell^\infty(G)$ be the Banach space of bounded functions $G\to\mathbb{C}$ with the supremum norm $\|b\|$. For $g\in G$ and $b\in\ell^\infty(G)$ let $\lambda_gb$ be the left translate, $(\lambda_gb)(x)=b(g^{-1}x)$, and write $\mathbf 1$ for the constant function $1$. Call a functional $m$ on $\ell^\infty(G)$ *positive* if $m(b)$ is a nonnegative real number whenever every value $b(x)$ is a nonnegative real number.
--
--   Assume that for every finite set $S\subseteq G$ and every $\varepsilon>0$ there is a continuous $\mathbb{C}$-linear functional $m:\ell^\infty(G)\to\mathbb{C}$ with $\|m\|\le1$, $m(\mathbf 1)=1$, $m$ positive, and
--   $$|m(\lambda_gb)-m(b)|\le\varepsilon\,\|b\|\qquad\text{for all }g\in S\text{ and }b\in\ell^\infty(G).$$
--   Then $G$ is amenable: there is a $\mathbb{C}$-linear functional $M$ on $\ell^\infty(G)$ with $M(\mathbf 1)=1$, such that $M(b)$ is a nonnegative real number whenever every value $b(x)$ is a nonnegative real number, and such that $M(\lambda_gb)=M(b)$ for all $g\in G$ and $b\in\ell^\infty(G)$.
--
--   So, to prove amenability it suffices to produce, for each finite set of translations and each tolerance, a positive normalized functional of norm at most one that is almost invariant under those translations, with an error proportional to $\|b\|$. This is the form in which almost invariant vectors of the regular representation are turned into an invariant mean.
--
--   **Formalization Note** $\ell^\infty(G)$ is the space `G →ᵇ ℂ` of bounded continuous functions, every function being continuous for the discrete topology, and $\lambda_gb$ is `leftTranslate g b`. Positivity is expressed through real and imaginary parts: real part $\ge0$ and imaginary part $=0$. The conclusion `Amenable G` asks only for a linear functional, with no continuity requirement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/CompactMean.lean#L14-L83

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

open OAI OAI.Dixmier
open Filter Topology
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem OAI.Dixmier.amenable_of_approximate_means
    (h : ∀ (S : Finset G) (ε : ℝ), 0 < ε →
      ∃ m : (G →ᵇ ℂ) →L[ℂ] ℂ,
        ‖m‖ ≤ 1 ∧ m (BoundedContinuousFunction.const G (1 : ℂ)) = 1 ∧
        (∀ b : G →ᵇ ℂ, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) →
          0 ≤ (m b).re ∧ (m b).im = 0) ∧
        ∀ g ∈ S, ∀ b : G →ᵇ ℂ, ‖m (leftTranslate g b) - m b‖ ≤ ε * ‖b‖) :
    Amenable G := by sorry
