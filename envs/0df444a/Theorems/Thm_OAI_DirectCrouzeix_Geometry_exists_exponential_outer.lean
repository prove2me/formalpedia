-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_exists_exponential_outer
-- name    : OAI.DirectCrouzeix.Geometry.exists_exponential_outer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:42:28.708413+00:00
-- url     : https://prove2.me/theorems/5dcdbb83-cce9-4f48-b608-23819629ee0b
-- title:
--   Outer approximation of a compact convex planar set by a compact sublevel set of an exponential sum
-- statement:
--   Identify $\mathbb{C}$ with $\mathbb{R}^2$ and write $\langle z,w\rangle=\operatorname{Re}(\overline{z}\,w)$ for the real inner product. For a finite set $D\subset\mathbb{C}$ and families $v=(v_\nu)_{\nu\in D}$ in $\mathbb{C}$ and $b=(b_\nu)_{\nu\in D}$ in $\mathbb{R}$, consider the exponential sum
--
--   $$
--   \varphi_{v,b}(z)=\sum_{\nu\in D}\exp\big(\langle v_\nu,z\rangle+b_\nu\big),\qquad z\in\mathbb{C}.
--   $$
--
--   **Theorem.** Let $K\subseteq\mathbb{C}$ be a nonempty, compact, convex set and let $\varepsilon>0$. Then there exist a finite set $D\subset\mathbb{C}$ and families $v\in\mathbb{C}^D$, $b\in\mathbb{R}^D$ such that $\varphi=\varphi_{v,b}$ satisfies:
--
--   1. $\varphi(z)<1$ for every $z\in K$;
--   2. the sublevel set $\Omega=\{z\in\mathbb{C}:\varphi(z)\le1\}$ is compact;
--   3. every $z$ with $\varphi(z)\le1$ lies within distance less than $\varepsilon$ of $K$: there is $w\in K$ with $|z-w|<\varepsilon$.
--
--   In short,
--
--   $$
--   K\subseteq\{z:\varphi(z)<1\}\subseteq\{z:\varphi(z)\le1\}\subseteq\bigcup_{w\in K}\{z:|z-w|<\varepsilon\},\qquad \{z:\varphi(z)\le1\}\ \text{compact}.
--   $$
--
--   The function $\varphi$ is smooth and convex (a finite sum of exponentials of affine functions), so the theorem replaces an arbitrary compact convex set, such as the numerical range of a matrix, by a slightly larger compact sublevel set of a smooth convex function that contains $K$ in its strict sublevel set $\{\varphi<1\}$. Such domains are regular enough for conformal-mapping and Faber-polynomial arguments, while still being $\varepsilon$-close to $K$, so estimates proved on them pass to $K$ by letting $\varepsilon\to0$.
--
--   **Formalization Note** The index set is a `Finset ℂ` $D$, and $v$, $b$ are functions on the corresponding subtype; the statement only asserts their existence (in the construction $D$ consists of unit vectors). The inner product is Mathlib's real inner product `inner ℝ` on $\mathbb{C}$, and the exponential sum is `expLevel v b`. Convexity of $K$ is convexity over $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/OuterApproximation.lean#L59-L122

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_OuterApproximation

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
open Set
open scoped ComplexConjugate Matrix

theorem OAI.DirectCrouzeix.Geometry.exists_exponential_outer {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hv : Convex ℝ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (D : Finset ℂ) (v : D → ℂ) (b : D → ℝ),
      (∀ z ∈ K, expLevel v b z < 1) ∧
      IsCompact {z | expLevel v b z ≤ 1} ∧
      (∀ z, expLevel v b z ≤ 1 → ∃ w ∈ K, ‖z-w‖ < ε) := by sorry
