-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_direction_net_distance
-- name    : OAI.DirectCrouzeix.Geometry.direction_net_distance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:37:13.567148+00:00
-- url     : https://prove2.me/theorems/6aa370ff-ec04-4046-a596-aae9eaaeadf3
-- title:
--   Approximate support inequalities along a $\delta$-net of directions force proximity to a compact convex set
-- statement:
--   Equip $\mathbb{C}$ with the real inner product $\langle\mu,z\rangle=\operatorname{Re}(\overline{\mu}\,z)=\operatorname{Re}\mu\,\operatorname{Re}z+\operatorname{Im}\mu\,\operatorname{Im}z$. For a set $K\subseteq\mathbb{C}$ and a direction $\mu\in\mathbb{C}$, the support function of $K$ is
--
--   $$
--   h_K(\mu)=\sup_{w\in K}\,\langle\mu,w\rangle .
--   $$
--
--   **Theorem.** Let $K\subseteq\mathbb{C}$ be nonempty, compact and convex, let $D\subseteq\mathbb{C}$ be a finite set, and let $\delta,M,L$ be real numbers with $\delta>0$. Assume
--
--   1. $|w|\le M$ for every $w\in K$;
--   2. for every $\nu\in\mathbb{C}$ with $|\nu|=1$ there is $\mu\in D$ with $|\nu-\mu|<\delta$;
--   3. $z\in\mathbb{C}$ satisfies $|z|\le L$ and $\langle\mu,z\rangle\le h_K(\mu)+\delta$ for every $\mu\in D$.
--
--   Then there is a point $w\in K$ with
--
--   $$
--   |z-w|\le\delta\,(1+L+M).
--   $$
--
--   The elements of $D$ are not required to have modulus $1$. The theorem says that a point satisfying, up to an error $\delta$, the supporting half-plane inequalities of $K$ in the finitely many directions of a $\delta$-net lies within distance $\delta(1+L+M)$ of $K$. It is the key estimate showing that regions cut out by finitely many approximate support constraints, such as sublevel sets of suitable sums of exponentials, are uniformly close outer approximations of $K$.
--
--   **Formalization Note** The support function is `convexSupport K μ`, defined as the real supremum `sSup` of $\langle\mu,w\rangle$ over $w\in K$; for nonempty compact $K$ it is an attained maximum, so Lean's convention for suprema of unbounded sets plays no role. The set $D$ is a `Finset ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean#L96-L139

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

theorem OAI.DirectCrouzeix.Geometry.direction_net_distance {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {D : Finset ℂ} {δ M L : ℝ} (hδ : 0 < δ)
    (hM : ∀ w ∈ K, ‖w‖ ≤ M)
    (hnet : ∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ)
    {z : ℂ} (hz : ‖z‖ ≤ L)
    (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ∃ w ∈ K, ‖z-w‖ ≤ δ*(1+L+M) := by sorry
