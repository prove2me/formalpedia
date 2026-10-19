-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_exists_axis_net
-- name    : OAI.DirectCrouzeix.Geometry.exists_axis_net
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:36:33.981983+00:00
-- url     : https://prove2.me/theorems/38145a7a-f995-4f13-85ba-78f079c098a6
-- title:
--   Finite $\delta$-nets of the unit circle containing the four axis directions
-- statement:
--   **Theorem.** For every real number $\delta>0$ there is a finite set $D\subseteq\mathbb{C}$ such that
--
--   1. every element of $D$ has modulus $1$;
--   2. the four axis directions $1,\,-1,\,i,\,-i$ belong to $D$;
--   3. $D$ is a $\delta$-net of the unit circle: for every $\nu\in\mathbb{C}$ with $|\nu|=1$ there is $\mu\in D$ with
--
--   $$
--   |\nu-\mu|<\delta .
--   $$
--
--   Finite direction sets of this kind discretize the support function of a planar convex set. The $\delta$-density ensures that finitely many supporting half-planes in the directions of $D$ already approximate a compact convex set to within $O(\delta)$, while the four axis directions give a crude a priori bound on the size of the resulting polygon-like region. Such nets are used to build outer approximations of compact convex sets by sublevel sets of sums of exponentials.
--
--   **Formalization Note** The set $D$ is a `Finset ℂ`, and the imaginary unit is `Complex.I`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean#L53-L77

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate

theorem OAI.DirectCrouzeix.Geometry.exists_axis_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : Finset ℂ, (∀ ν ∈ D, ‖ν‖ = 1) ∧ 1 ∈ D ∧ -1 ∈ D ∧
      Complex.I ∈ D ∧ -Complex.I ∈ D ∧
      (∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ) := by sorry
