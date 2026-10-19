-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_normalized_implicit_graph
-- name    : OAI.DirectCrouzeix.Geometry.normalized_implicit_graph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:20:51.177221+00:00
-- url     : https://prove2.me/theorems/18c95840-88a7-4e3d-b7be-f48dc0c73aa3
-- title:
--   Analytic implicit function for the level set $F(z,w)=1$ with horizontal tangent and real symmetry
-- statement:
--   Let $F:\mathbb{C}^2\to\mathbb{C}$ be analytic at the origin with $F(0,0)=1$. Let $b>0$ be a real number and assume that the complex derivative of $F$ at the origin is the linear map $(h_1,h_2)\mapsto b\,h_2$, that is,
--   $$
--   \frac{\partial F}{\partial z_1}(0,0)=0,\qquad \frac{\partial F}{\partial z_2}(0,0)=b .
--   $$
--   Assume also that $F$ commutes with complex conjugation: $F(\overline{z_1},\overline{z_2})=\overline{F(z_1,z_2)}$ for all $(z_1,z_2)\in\mathbb{C}^2$. Then there is a function $g:\mathbb{C}\to\mathbb{C}$, analytic at $0$, with $g(0)=0$ and $g'(0)=0$, such that for all $z$ in a neighbourhood of $0$
--
--   $$
--   F\bigl(z,g(z)\bigr)=1\qquad\text{and}\qquad g(\overline{z})=\overline{g(z)} .
--   $$
--
--   Thus near the origin the level set $\{F=1\}$ contains the graph of an analytic function $w=g(z)$ that is tangent to the $z_1$-axis at the origin, and by the symmetry $g$ takes real values at real points close to $0$. In the surrounding development this is used to parametrize level curves of sums of exponentials of affine functions near one of their points by an analytic map, through a complexification of the defining function.
--
--   **Formalization Note** The space $\mathbb{C}^2$ is the product `ℂ × ℂ`, the derivative hypothesis is `HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0`, and conjugation of a pair is the auxiliary function `conjugatePair`. The two neighbourhood statements are separate `∀ᶠ z in 𝓝 0` assertions; together they hold on a common neighbourhood of $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean#L60-L124

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Geometry
universe u_133 u_134 u_135
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate

theorem OAI.DirectCrouzeix.Geometry.normalized_implicit_graph {F : ℂ × ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hF0 : F 0 = 1) {b : ℝ} (hb : 0 < b)
    (hd : HasFDerivAt F ((b:ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ) 0)
    (hconj : ∀ z, F (conjugatePair z) = conj (F z)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, F (z,g z) = 1) ∧
      (∀ᶠ z in 𝓝 0, g (conj z) = conj (g z)) := by sorry
