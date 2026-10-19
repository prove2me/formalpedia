-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_inverseExterior_bounded
-- name    : OAI.DirectCrouzeix.Geometry.inverseExterior_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:30:36.143423+00:00
-- url     : https://prove2.me/theorems/7af01803-4c7d-4286-9cd1-6b588aceacf6
-- title:
--   The inverted exterior about a point of the open sublevel region is bounded
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{R}$ be a function and let $a\in\mathbb{C}$. The *inverted exterior* of $f$ about $a$ is the set
--
--   $$
--   U_f(a)=\{0\}\cup\Bigl\{w\in\mathbb{C}\setminus\{0\}:\ f\Bigl(a+\frac1w\Bigr)>1\Bigr\}.
--   $$
--
--   It is the image of the superlevel region $\{z\neq a:\ f(z)>1\}$ under the inversion $z\mapsto1/(z-a)$, with the point at infinity represented by $w=0$.
--
--   **Theorem.** Suppose that $f$ is continuous and that $a\in\mathbb{C}$ satisfies $f(a)<1$. Then there is a radius $L>0$ such that
--
--   $$
--   U_f(a)\subseteq\{w\in\mathbb{C}:\ |w|\le L\}.
--   $$
--
--   Geometrically, inverting about a point of the open region $\{f<1\}$ keeps the image of the region $\{f>1\}$ away from infinity. Consequently $U_f(a)$ has compact closure and is not the whole plane, two of the hypotheses under which the Riemann mapping theorem and its boundary-extension refinements are applied to $U_f(a)$. No compactness of the sublevel set is needed here.
--
--   **Formalization Note** The inverted exterior is `inverseExterior f a`, defined as the set of $w$ with `w = 0 ∨ 1 < f (a + w⁻¹)`; since the first alternative already covers $w=0$, Lean's convention that the inverse of $0$ is $0$ plays no role. The closed disk is `closedBall 0 L`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean#L112-L127

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

theorem OAI.DirectCrouzeix.Geometry.inverseExterior_bounded {f : ℂ → ℝ} (hf : Continuous f)
    {a : ℂ} (ha : f a < 1) : ∃ L > 0, inverseExterior f a ⊆ closedBall 0 L := by sorry
