-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_convex
-- name    : OAI.DirectCrouzeix.Geometry.expLevel_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:24:58.944855+00:00
-- url     : https://prove2.me/theorems/2c92be8a-c05a-4758-a790-d261767fdfaa
-- title:
--   Convexity of a sum of exponentials of real-affine functions on $\mathbb{C}$
-- statement:
--   Let $\iota$ be a finite index set, and let $v_i\in\mathbb{C}$ and $b_i\in\mathbb{R}$ for $i\in\iota$. Regard $\mathbb{C}$ as the real plane with the inner product $\langle u,z\rangle=\operatorname{Re}(\overline{u}\,z)=\operatorname{Re}u\,\operatorname{Re}z+\operatorname{Im}u\,\operatorname{Im}z$, and let
--   $$
--   L(z)=\sum_{i\in\iota}e^{\langle v_i,z\rangle+b_i}\qquad(z\in\mathbb{C}).
--   $$
--   Then $L$ is a convex function on all of $\mathbb{C}$, viewed as a real vector space: for all $x,y\in\mathbb{C}$ and all real $\alpha,\beta\ge0$ with $\alpha+\beta=1$,
--
--   $$
--   L(\alpha x+\beta y)\le\alpha L(x)+\beta L(y).
--   $$
--
--   Consequently the sublevel sets $\{L<1\}$ and $\{L\le1\}$ are convex. In the surrounding development such sublevel sets serve as smooth convex outer approximations of compact convex sets, in particular of the numerical range of a matrix, and convexity of $L$ is also used to show that the domains to which the Riemann mapping theorem is applied, obtained from the exterior $\{L>1\}$ by an inversion, are simply connected.
--
--   **Formalization Note** $L$ is `expLevel v b` with `v : ι → ℂ`, `b : ι → ℝ` and `[Fintype ι]`, and $\langle\cdot,\cdot\rangle$ is `inner ℝ` on $\mathbb{C}$. The statement is `ConvexOn ℝ univ (expLevel v b)`, which also records that the domain $\mathbb{C}$ is convex.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExponentialLevels.lean#L77-L89

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

theorem OAI.DirectCrouzeix.Geometry.expLevel_convex (v : ι → ℂ) (b : ι → ℝ) : ConvexOn ℝ univ (expLevel v b) := by sorry
