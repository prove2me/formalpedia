-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_negative_vertical_level_side
-- name    : OAI.DirectCrouzeix.Geometry.negative_vertical_level_side
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:21:28.278076+00:00
-- url     : https://prove2.me/theorems/8a40f8c4-3aae-4460-9981-72971dc58f3e
-- title:
--   Sides of a level curve that contains a real interval and has negative vertical derivative
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{R}$, regarded as a function of the two real variables $x=\operatorname{Re}z$ and $y=\operatorname{Im}z$, be continuously differentiable on a neighbourhood of $0$. Assume that its derivative at $0$ in the direction of the vector $i$ is negative,
--   $$
--   Df(0)[i]=\frac{\partial f}{\partial y}(0)<0,
--   $$
--   and that $f(x)=1$ for all real numbers $x$ in some neighbourhood of $0$. Then there is $r>0$ such that for every $z\in\mathbb{C}$ with $|z|<r$
--
--   $$
--   f(z)<1\iff\operatorname{Im}z>0\qquad\text{and}\qquad f(z)>1\iff\operatorname{Im}z<0 .
--   $$
--
--   So, within the disk $|z|<r$, the level set $\{f=1\}$ is exactly the real axis, the sublevel set $\{f<1\}$ is the upper half and the superlevel set $\{f>1\}$ is the lower half. This is used to decide on which side of a boundary curve, after it has been straightened to the real axis by an analytic change of variables, a sublevel domain lies, which is the side condition required of an analytic boundary chart.
--
--   **Formalization Note** The regularity hypothesis is `ContDiffAt ℝ 1 f 0`, i.e. $f$ is differentiable with continuous derivative on a neighbourhood of $0$; the derivative condition is `fderiv ℝ f 0 Complex.I < 0`, the real Fréchet derivative at $0$ evaluated at the vector $i$; and real numbers are embedded in $\mathbb{C}$ by the usual coercion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean#L130-L181

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

theorem OAI.DirectCrouzeix.Geometry.negative_vertical_level_side {f : ℂ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0) (hd : fderiv ℝ f 0 Complex.I < 0)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, f (x:ℂ) = 1) :
    ∃ r > 0, ∀ z ∈ ball (0:ℂ) r, (f z < 1 ↔ 0 < z.im) ∧ (1 < f z ↔ z.im < 0) := by sorry
