-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_axis_support_bound
-- name    : OAI.DirectCrouzeix.Geometry.axis_support_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:37:57.860201+00:00
-- url     : https://prove2.me/theorems/cf24a025-ff74-47f3-8696-3937a0d6bef9
-- title:
--   Approximate support inequalities in the four axis directions bound $|z|$ by $2(M+\delta)$
-- statement:
--   Equip $\mathbb{C}$ with the real inner product $\langle\mu,z\rangle=\operatorname{Re}(\overline{\mu}\,z)=\operatorname{Re}\mu\,\operatorname{Re}z+\operatorname{Im}\mu\,\operatorname{Im}z$. For a set $K\subseteq\mathbb{C}$ and a direction $\mu\in\mathbb{C}$, the support function of $K$ is
--
--   $$
--   h_K(\mu)=\sup_{w\in K}\,\langle\mu,w\rangle .
--   $$
--
--   **Theorem.** Let $K\subseteq\mathbb{C}$ be nonempty, let $M,\delta\in\mathbb{R}$, and assume $|w|\le M$ for every $w\in K$. Let $D\subseteq\mathbb{C}$ be a finite set containing the four axis directions $1,-1,i,-i$, and let $z\in\mathbb{C}$ satisfy $\langle\mu,z\rangle\le h_K(\mu)+\delta$ for every $\mu\in D$. Then
--
--   $$
--   |z|\le2\,(M+\delta).
--   $$
--
--   No sign condition on $\delta$ and no compactness or convexity of $K$ is required. The result gives an a priori bound: a point that satisfies the supporting half-plane inequalities of a set contained in the disk of radius $M$ up to an error $\delta$, at least in the four axis directions, lies in the disk of radius $2(M+\delta)$. It provides the radius $L$ needed when such points are compared with $K$ using a $\delta$-net of directions.
--
--   **Formalization Note** The support function is `convexSupport K μ`, the real supremum `sSup` of $\langle\mu,w\rangle$ over $w\in K$; as $K$ is nonempty and bounded this is a genuine finite supremum. The set $D$ is a `Finset ℂ`, of which only the membership of the four axis directions is used.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean#L141-L158

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

theorem OAI.DirectCrouzeix.Geometry.axis_support_bound {K : Set ℂ} (hne : K.Nonempty) {M δ : ℝ}
    (hM : ∀ w ∈ K, ‖w‖ ≤ M) {D : Finset ℂ}
    (h1 : 1 ∈ D) (hm1 : -1 ∈ D) (hI : Complex.I ∈ D) (hmI : -Complex.I ∈ D)
    {z : ℂ} (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ‖z‖ ≤ 2*(M+δ) := by sorry
