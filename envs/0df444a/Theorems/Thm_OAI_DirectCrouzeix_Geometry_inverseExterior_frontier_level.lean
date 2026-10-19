-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_inverseExterior_frontier_level
-- name    : OAI.DirectCrouzeix.Geometry.inverseExterior_frontier_level
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:31:34.645384+00:00
-- url     : https://prove2.me/theorems/4c9e0e05-c8fc-44c1-ac25-d042e771f4bb
-- title:
--   Boundary points of the inverted exterior come from the level set $f=1$
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{R}$ be a function and let $a\in\mathbb{C}$. The *inverted exterior* of $f$ about $a$ is the set
--
--   $$
--   U_f(a)=\{0\}\cup\Bigl\{w\in\mathbb{C}\setminus\{0\}:\ f\Bigl(a+\frac1w\Bigr)>1\Bigr\}.
--   $$
--
--   It is the image of the superlevel region $\{z\neq a:\ f(z)>1\}$ under the inversion $z\mapsto1/(z-a)$, with the point at infinity represented by $w=0$.
--
--   **Theorem.** Suppose that $f$ is continuous and that the sublevel set $\{z\in\mathbb{C}:\ f(z)\le1\}$ is compact. Let $a,w\in\mathbb{C}$ and suppose that $w$ lies in the topological boundary $\partial U_f(a)=\overline{U_f(a)}\setminus\operatorname{int}U_f(a)$. Then
--
--   $$
--   w\neq0\qquad\text{and}\qquad f\Bigl(a+\frac1w\Bigr)=1 .
--   $$
--
--   In other words, undoing the inversion sends every boundary point of $U_f(a)$ to a point of the level set $\{f=1\}$. This is how boundary information transfers: a conformal map onto $U_f(a)$ that extends to the closed disk sends the unit circle into $\partial U_f(a)$, so after inversion it parametrizes points of the level curve $\{f=1\}$.
--
--   **Formalization Note** The inverted exterior is `inverseExterior f a`, defined as the set of $w$ with `w = 0 ∨ 1 < f (a + w⁻¹)`; since the first alternative already covers $w=0$, Lean's convention that the inverse of $0$ is $0$ plays no role. The boundary is Mathlib's `frontier`, the closure minus the interior.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean#L143-L159

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

theorem OAI.DirectCrouzeix.Geometry.inverseExterior_frontier_level {f : ℂ → ℝ} (hf : Continuous f)
    (hc : IsCompact {z | f z ≤ 1}) {a w : ℂ}
    (hw : w ∈ frontier (inverseExterior f a)) : w ≠ 0 ∧ f (a+w⁻¹) = 1 := by sorry
