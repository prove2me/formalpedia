-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_holomorphic_support
-- name    : OAI.DirectCrouzeix.Geometry.expLevel_holomorphic_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:41:07.449166+00:00
-- url     : https://prove2.me/theorems/8ceda503-d157-4182-b670-76003c88ac7a
-- title:
--   The vector $\zeta\psi'(\zeta)$ is an outward normal of an exponential-sum sublevel set at the boundary point $\psi(\zeta)$
-- statement:
--   Identify $\mathbb{C}$ with the Euclidean plane $\mathbb{R}^2$ and write $\langle z,w\rangle=\operatorname{Re}(\overline{z}\,w)$ for the real inner product. Let $I$ be a finite index set, let $v_i\in\mathbb{C}$ and $b_i\in\mathbb{R}$ for $i\in I$, and consider the exponential sum
--
--   $$
--   \varphi(z)=\sum_{i\in I}\exp\big(\langle v_i,z\rangle+b_i\big),\qquad z\in\mathbb{C}.
--   $$
--
--   Assume that $\varphi(a)<1$ for some point $a\in\mathbb{C}$. Let $\psi:\mathbb{C}\to\mathbb{C}$ be a function and $\zeta\in\mathbb{C}$ a point with $|\zeta|=1$ such that
--
--   1. $\psi$ is complex differentiable at $\zeta$ and $\psi'(\zeta)\neq0$;
--   2. $\varphi(\psi(\eta))=1$ for every $\eta\in\mathbb{C}$ with $|\eta|=1$;
--   3. $\varphi(\psi(\eta))\ge1$ for every $\eta\in\mathbb{C}$ with $|\eta|\ge1$.
--
--   Then for every $w\in\mathbb{C}$ with $\varphi(w)\le1$,
--
--   $$
--   \big\langle \zeta\,\psi'(\zeta),\ \psi(\zeta)-w\big\rangle=\operatorname{Re}\Big(\overline{\zeta\,\psi'(\zeta)}\,\big(\psi(\zeta)-w\big)\Big)\ \ge\ 0 .
--   $$
--
--   Equivalently, the sublevel set $\Omega=\{w\in\mathbb{C}:\varphi(w)\le1\}$ is contained in the closed half-plane $\{w:\langle\zeta\psi'(\zeta),\,w-\psi(\zeta)\rangle\le0\}$: the vector $\zeta\psi'(\zeta)$, which is the image under $\psi'(\zeta)$ of the outward radial direction $\zeta$ of the unit circle, is an outward normal of $\Omega$ at the boundary point $\psi(\zeta)$.
--
--   The typical application is to an exterior conformal map $\psi$ that sends the unit circle onto the level curve $\{\varphi=1\}$ and the exterior of the unit disk outside $\Omega$. The inequality converts the convexity of $\Omega$ into the sign conditions $\operatorname{Re}\big(\overline{n}\,(\psi(\zeta)-w)\big)\ge0$, with $n=\zeta\psi'(\zeta)$, that are needed for operator-theoretic estimates on such domains, for instance positivity of the Hermitian part of $n\,(\psi(\zeta)I-A)^{-1}$ when the numerical range of a matrix $A$ lies in $\Omega$, or nonnegativity of a boundary kernel built from $\psi$.
--
--   **Formalization Note** The index type is an arbitrary `Fintype` and the inner product is Mathlib's real inner product `inner ℝ` on $\mathbb{C}$, which equals $\operatorname{Re}(\overline{z}w)$. No regularity of $\psi$ away from $\zeta$ is assumed: differentiability enters only as `HasDerivAt ψ (deriv ψ ζ) ζ` (a complex derivative at the single point $\zeta$) together with `deriv ψ ζ ≠ 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExponentialSupport.lean#L87-L149

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
universe u_143
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

theorem OAI.DirectCrouzeix.Geometry.expLevel_holomorphic_support {ι : Type u_143} [Fintype ι]
    (v : ι → ℂ) (b : ι → ℝ) {a : ℂ} (ha : expLevel v b a < 1)
    {ψ : ℂ → ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hd : HasDerivAt ψ (deriv ψ ζ) ζ) (hdn : deriv ψ ζ ≠ 0)
    (hcircle : ∀ η : ℂ, ‖η‖ = 1 → expLevel v b (ψ η) = 1)
    (hout : ∀ η : ℂ, 1 ≤ ‖η‖ → 1 ≤ expLevel v b (ψ η))
    {w : ℂ} (hw : expLevel v b w ≤ 1) :
    0 ≤ inner ℝ (ζ*deriv ψ ζ) (ψ ζ-w) := by sorry
