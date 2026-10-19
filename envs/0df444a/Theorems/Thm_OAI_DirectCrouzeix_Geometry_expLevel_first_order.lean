-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_first_order
-- name    : OAI.DirectCrouzeix.Geometry.expLevel_first_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:24:15.832501+00:00
-- url     : https://prove2.me/theorems/9e543309-6926-449e-8de5-804604216ca6
-- title:
--   Tangent-plane inequality for a sum of exponentials of real-affine functions on $\mathbb{C}$
-- statement:
--   Let $\iota$ be a finite index set, and let $v_i\in\mathbb{C}$ and $b_i\in\mathbb{R}$ for $i\in\iota$. Regard $\mathbb{C}$ as the Euclidean plane with the real inner product
--   $$
--   \langle u,z\rangle=\operatorname{Re}(\overline{u}\,z)=\operatorname{Re}u\,\operatorname{Re}z+\operatorname{Im}u\,\operatorname{Im}z ,
--   $$
--   and define $L:\mathbb{C}\to\mathbb{R}$ and $\nabla L:\mathbb{C}\to\mathbb{C}$ by
--   $$
--   L(z)=\sum_{i\in\iota}e^{\langle v_i,z\rangle+b_i},\qquad \nabla L(z)=\sum_{i\in\iota}e^{\langle v_i,z\rangle+b_i}\,v_i .
--   $$
--   Then for all $z,w\in\mathbb{C}$
--
--   $$
--   L(z)+\langle\nabla L(z),\,w-z\rangle\le L(w).
--   $$
--
--   The vector $\nabla L(z)$ is the gradient of $L$ at $z$ with respect to this inner product, so the inequality says that the tangent plane to the graph of $L$ at any point lies below the graph; it is the first-order form of the convexity of $L$. Two direct consequences are used later: $\nabla L(p)\neq0$ whenever $L(p)=1$ and $L(a)<1$ for some $a$, so the level curve $\{L=1\}$ has no critical points as soon as $\{L<1\}$ is nonempty; and if $L(p)=1$, the sublevel set $\{L\le1\}$ lies in the half-plane $\{w:\langle\nabla L(p),w-p\rangle\le0\}$.
--
--   **Formalization Note** $L$ and $\nabla L$ are `expLevel v b` and `expGradient v b` with `v : ι → ℂ`, `b : ι → ℝ` and `[Fintype ι]`, and $\langle\cdot,\cdot\rangle$ is `inner ℝ` on $\mathbb{C}$. For empty $\iota$ both sides of the inequality are $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExponentialLevels.lean#L55-L68

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
universe u_135 u_136 u_137
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
variable {ι : Type u_135} [Fintype ι]

theorem OAI.DirectCrouzeix.Geometry.expLevel_first_order (v : ι → ℂ) (b : ι → ℝ) (z w : ℂ) :
    expLevel v b z + inner ℝ (expGradient v b z) (w-z) ≤ expLevel v b w := by sorry
