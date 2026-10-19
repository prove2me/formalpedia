-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Geometry_expLevel_boundary_parametrization
-- name    : OAI.DirectCrouzeix.Geometry.expLevel_boundary_parametrization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:27:00.246025+00:00
-- url     : https://prove2.me/theorems/5bd0a77d-6796-4a66-bf62-bf3537a7a69f
-- title:
--   Holomorphic chart straightening the level curve $E=1$ of an exponential sum, with $\{E<1\}$ on the upper side
-- statement:
--   Let $\iota$ be a finite index set, let $v=(v_i)_{i\in\iota}$ be complex numbers and $b=(b_i)_{i\in\iota}$ real numbers. Regard $\mathbb{C}$ as the Euclidean plane with the real inner product $\langle w,z\rangle=\operatorname{Re}(\overline{w}\,z)=\operatorname{Re}w\,\operatorname{Re}z+\operatorname{Im}w\,\operatorname{Im}z$, and consider the exponential sum
--
--   $$
--   E(z)=\sum_{i\in\iota}\exp\bigl(\langle v_i,z\rangle+b_i\bigr),\qquad z\in\mathbb{C},
--   $$
--
--   which is a smooth convex function from $\mathbb{C}$ to $\mathbb{R}$.
--
--   **Theorem.** Let $p,a\in\mathbb{C}$ satisfy $E(p)=1$ and $E(a)<1$. Then there is a function $H:\mathbb{C}\to\mathbb{C}$ that is complex-analytic at $0$ (it is given by a convergent power series in a neighbourhood of $0$) with
--
--   $$
--   H(0)=p,\qquad H'(0)\neq0,
--   $$
--
--   and there is a neighbourhood $N$ of $0$ in $\mathbb{C}$ such that for every $z\in N$
--
--   $$
--   E(H(z))<1\iff\operatorname{Im}z>0,\qquad\qquad E(H(z))>1\iff\operatorname{Im}z<0 .
--   $$
--
--   Consequently, for $z\in N$ one has $E(H(z))=1$ exactly when $z$ is real.
--
--   Thus near any point $p$ of the level curve $\{E=1\}$ there is a holomorphic local coordinate in which this curve becomes the real axis, the sublevel region $\{E<1\}$ becomes the upper half-plane and the region $\{E>1\}$ becomes the lower half-plane. The point $a$ with $E(a)<1$ only serves to guarantee that $p$ is not a critical point of $E$. Charts of this kind show that the boundary of the convex domain $\{E<1\}$ is a real-analytic curve, which is what is needed to continue Riemann maps of such domains, or of their exteriors, analytically across the boundary.
--
--   **Formalization Note** The exponential sum is `expLevel v b`, with $\langle v_i,z\rangle$ written `inner ℝ (v i) z` for $\mathbb{C}$ viewed as a real inner product space, and the index type carries a `Fintype` instance. Analyticity is `AnalyticAt ℂ H 0`, $H'(0)$ is the complex derivative `deriv H 0`, and the two equivalences are asserted eventually in the neighbourhood filter `𝓝 0`. The function $H$ is defined on all of $\mathbb{C}$, but only its behaviour near $0$ is constrained.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryParametrization.lean#L39-L129

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
universe u_137
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology ComplexConjugate
variable {ι : Type u_137} [Fintype ι]

theorem OAI.DirectCrouzeix.Geometry.expLevel_boundary_parametrization (v : ι → ℂ) (b : ι → ℝ) {p a : ℂ}
    (hp : expLevel v b p = 1) (ha : expLevel v b a < 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = p ∧ deriv H 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, (expLevel v b (H z) < 1 ↔ 0 < z.im) ∧
        (1 < expLevel v b (H z) ↔ z.im < 0)) := by sorry
