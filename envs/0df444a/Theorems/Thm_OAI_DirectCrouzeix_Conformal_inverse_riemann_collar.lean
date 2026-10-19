-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_inverse_riemann_collar
-- name    : OAI.DirectCrouzeix.Conformal.inverse_riemann_collar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:17:04.155979+00:00
-- url     : https://prove2.me/theorems/dbebaa3b-35e8-415d-a644-b545a0d9f7bd
-- title:
--   Conformal collar: the inverse Riemann map of a bounded domain with analytic boundary extends univalently past the unit circle
-- statement:
--   Let $U\subseteq\mathbb{C}$ be an open set whose closure $\overline{U}$ is compact (that is, $U$ is bounded), and write $\partial U=\overline{U}\setminus U$ for its boundary, $\mathbb{D}=\{w\in\mathbb{C}:|w|<1\}$, $\overline{\mathbb{D}}=\{w\in\mathbb{C}:|w|\le1\}$ and $D(0,R)=\{w\in\mathbb{C}:|w|<R\}$. Assume that $U$ *has analytic boundary*: for every $p\in\partial U$ there is an analytic boundary chart of $U$ at $p$, i.e. open sets $\Sigma,T\subseteq\mathbb{C}$ and a homeomorphism $\varphi:\Sigma\to T$ with inverse $\psi:T\to\Sigma$ such that $0\in\Sigma$, $\varphi(0)=p$, $\varphi$ is analytic at every point of $\Sigma$, $\psi$ is analytic at every point of $T$, $\psi'(p)\neq0$, and $\varphi(z)\in U\iff\operatorname{Im}z>0$ for every $z\in\Sigma$.
--
--   Let $a\in U$ and let $f:\mathbb{C}\to\mathbb{C}$ be a normalized embedding of $U$ at $a$ (that is, $f$ is holomorphic and injective on $U$, maps $U$ into $\mathbb{D}$, has $f'(z)\neq0$ for all $z\in U$, and $f(a)=0$) with $f(U)=\mathbb{D}$. Then there exist a real number $R>1$ and a function $g:\mathbb{C}\to\mathbb{C}$, analytic and injective on $D(0,R)$, such that
--
--   $$
--   g(\mathbb{D})=U,\qquad g(\overline{\mathbb{D}})=\overline{U},\qquad g(0)=a,\qquad g'(z)\neq0\ \ \text{for all } z\in D(0,R).
--   $$
--
--   So the inverse $f^{-1}:\mathbb{D}\to U$ of the Riemann map extends to a conformal map of a disk of radius larger than $1$, a conformal collar around the unit circle; since $g$ is injective, it maps the unit circle onto $\partial U$. Combined with the existence of such a normalized embedding for simply connected proper open subsets of $\mathbb{C}$, this gives a collar map for every bounded simply connected domain with analytic boundary; in the surrounding development it is used to construct exterior conformal maps of smooth convex domains that continue analytically across the boundary curve.
--
--   **Formalization Note** The boundary hypothesis is `HasAnalyticBoundary U`, which asks for a term of `AnalyticBoundaryChart U p` at every point of `frontier U`; the chart is an `OpenPartialHomeomorph ℂ ℂ` and $\psi$ is its total inverse function `chart.symm`. The normalized embedding is `NormalizedEmbedding U a f`, with holomorphy stated as `DifferentiableOn ℂ f U`. Analyticity on a set is `AnalyticOnNhd ℂ`, injectivity on a set is `InjOn`, and derivatives are Lean's `deriv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ConformalCollar.lean#L129-L228

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.inverse_riemann_collar {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUB : HasAnalyticBoundary U)
    {a : ℂ} (ha : a ∈ U) {f : ℂ → ℂ} (hf : NormalizedEmbedding U a f)
    (hs : f '' U = ball 0 1) :
    ∃ R > 1, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R) ∧ InjOn g (ball 0 R) ∧
      g '' ball 0 1 = U ∧ g '' closedBall 0 1 = closure U ∧ g 0 = a ∧
      (∀ z ∈ ball 0 R, deriv g z ≠ 0) := by sorry
