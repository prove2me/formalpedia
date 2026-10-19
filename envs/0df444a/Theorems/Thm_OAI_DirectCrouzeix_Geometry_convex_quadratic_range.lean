-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_convex_quadratic_range
-- name    : OAI.DirectCrouzeix.Geometry.convex_quadratic_range
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:38:50.340225+00:00
-- url     : https://prove2.me/theorems/0161f2eb-3529-419a-b8af-c2689fb0f92d
-- title:
--   Toeplitz–Hausdorff theorem: the numerical range of a linear operator is convex
-- statement:
--   Let $\mathcal{E}$ be a complex inner product space whose inner product $\langle x,y\rangle$ is conjugate-linear in $x$ and linear in $y$; neither completeness nor finite dimension is assumed. Let $T:\mathcal{E}\to\mathcal{E}$ be a $\mathbb{C}$-linear map, not necessarily bounded. The numerical range of $T$ is
--
--   $$
--   W(T)=\bigl\{\langle x,Tx\rangle:\ x\in\mathcal{E},\ \|x\|=1\bigr\}\subseteq\mathbb{C}.
--   $$
--
--   **Theorem (Toeplitz–Hausdorff).** $W(T)$ is a convex subset of $\mathbb{C}$, viewed as a real vector space: for all $z,w\in W(T)$ and all real $r,s\ge0$ with $r+s=1$,
--
--   $$
--   r\,z+s\,w\in W(T).
--   $$
--
--   If $\mathcal{E}=\{0\}$ the set $W(T)$ is empty, and the statement holds trivially. Convexity of the numerical range is a basic structural fact in matrix and operator theory. Applied to $n\times n$ complex matrices acting on $\mathbb{C}^n$, it shows that the numerical range of a matrix is a compact convex set, which is what allows it to be approximated from outside by smooth convex domains.
--
--   **Formalization Note** The space is a type `E` with `[NormedAddCommGroup E] [InnerProductSpace ℂ E]`, the operator is `T : E →ₗ[ℂ] E`, the values are `inner ℂ x (T x)` (Mathlib's inner product is conjugate-linear in the first argument), and convexity is `Convex ℝ` of the set of these values over unit vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Convexity.lean#L201-L244

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Convexity

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
universe u_140 u_141 u_142
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
open Set
open scoped ComplexConjugate Matrix
variable {E : Type u_142} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem OAI.DirectCrouzeix.Geometry.convex_quadratic_range (T : E →ₗ[ℂ] E) :
    Convex ℝ {z : ℂ | ∃ x : E, ‖x‖ = 1 ∧ inner ℂ x (T x) = z} := by sorry
