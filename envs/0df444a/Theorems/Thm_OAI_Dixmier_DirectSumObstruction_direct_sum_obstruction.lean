-- Prove2me | Theorems.Thm_OAI_Dixmier_DirectSumObstruction_direct_sum_obstruction
-- name    : OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:32:09.908985+00:00
-- url     : https://prove2.me/theorems/75dca998-8c98-44f3-a28a-cbf25b95e4d7
-- title:
--   Direct-sum obstruction: stage operators with unbounded kernel energy give a $(1+\kappa)$-bounded representation not similar to a unitary one
-- statement:
--   Let $G$ be an arbitrary group (no countability or topology is assumed). For an integer $k\ge 1$ let $\mathcal H_k=\ell^2(G;\mathbb C^k)$ be the Hilbert space of functions $\xi:G\to\mathbb C^k$ with $\|\xi\|^2=\sum_{x\in G}\|\xi(x)\|^2<\infty$, and let $\lambda(g)$, $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$, be left translation, a unitary representation of $G$ on $\mathcal H_k$. For $x\in G$ write $\mathrm{ev}_x:\mathcal H_k\to\mathbb C^k$, $\xi\mapsto\xi(x)$, for evaluation at $x$, and $\iota_x:\mathbb C^k\to\mathcal H_k$ for the inclusion sending $v$ to the function equal to $v$ at $x$ and to $0$ elsewhere. For a bounded operator $F$ on $\mathcal H_k$ we use:
--
--   - its *row* $\mathrm{ev}_1F:\mathcal H_k\to\mathbb C^k$ and its *column* $F\iota_1:\mathbb C^k\to\mathcal H_k$ at the identity $1\in G$;
--   - its blocks $F_{x,y}=\mathrm{ev}_xF\iota_y\in M_k(\mathbb C)$ and its *kernel energy* $\mathcal E(F)=\sum_{s\in G}\|F_{1,s}\|_{\mathrm{HS}}^2$, where $\|M\|_{\mathrm{HS}}^2=\sum_{a,b}|M_{ab}|^2$ is the squared Hilbert–Schmidt (Frobenius) norm of a $k\times k$ matrix;
--   - its *coboundary* $g\mapsto F-\lambda(g)F\lambda(g^{-1})$.
--
--   Let $(k_j)_{j\in\mathbb N}$ be positive integers, let $\kappa\ge 0$ be real, and for every $j$ let $A_j,T_j$ be bounded operators on $\mathcal H_{k_j}$ such that, for all $j\in\mathbb N$ and all $g\in G$:
--
--   1. $A_j$ commutes with $\lambda(g)$;
--   2. $\|\mathrm{ev}_1T_j\|\le\kappa$ and $\|(A_j-T_j)\iota_1\|\le\kappa$;
--   3. $\|T_j-\lambda(g)T_j\lambda(g^{-1})\|\le\kappa$;
--
--   and assume that the kernel energy per fibre dimension is unbounded:
--
--   $$
--   \frac{\mathcal E(A_j)}{k_j}\longrightarrow+\infty\qquad(j\to\infty).
--   $$
--
--   Let $\mathcal H=\bigoplus_{j\in\mathbb N}\mathcal H_{k_j}$ be the Hilbert direct sum and $\mathcal K=\mathcal H\oplus\mathcal H$ with norm $\|(x,y)\|^2=\|x\|^2+\|y\|^2$. Then there is a group homomorphism $\pi$ from $G$ into the bounded operators on $\mathcal K$ such that
--
--   $$
--   \|\pi(g)\|\le 1+\kappa\quad\text{for every }g\in G,
--   $$
--
--   and $\pi$ is not similar to a unitary representation: there is no bounded invertible operator $S$ on $\mathcal K$ with bounded inverse such that $\|S\pi(g)S^{-1}x\|=\|x\|$ for all $g\in G$ and $x\in\mathcal K$.
--
--   The operators $A_j$ and $T_j$ are not required to be bounded uniformly in $j$; only their rows and columns at the identity and the coboundaries of $T_j$ are controlled by $\kappa$. This is the operator-theoretic core of the construction of uniformly bounded representations that are not unitarizable: it reduces the problem to finding, in each finite fibre dimension $k_j$, a translation-invariant operator $A_j$ that is $\kappa$-close in this row/column sense to an operator $T_j$ with $\kappa$-small coboundary, while the energy of $A_j$ is much larger than $k_j$.
--
--   **Formalization Note** The stage space is `KernelObstruction.Space G (Fin (k j))`, an `lp` space with Euclidean fibres, and the carrier `Carrier G k` is `WithLp 2 (H × H)` for the `lp` Hilbert sum `H` of the stages. The energy is an infinite sum (`tsum`) whose summand family is always summable, and $k_j$ is cast to a real number. The homomorphism is a monoid homomorphism into the continuous linear operators, and `SimilarToUnitary` asks for a continuous linear equivalence $S$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SumObstruction.lean#L25-L71

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
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction

open OAI OAI.Dixmier OAI.Dixmier.DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

theorem OAI.Dixmier.DirectSumObstruction.direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π := by sorry
