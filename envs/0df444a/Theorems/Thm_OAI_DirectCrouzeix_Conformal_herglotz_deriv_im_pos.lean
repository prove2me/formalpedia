-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_herglotz_deriv_im_pos
-- name    : OAI.DirectCrouzeix.Conformal.herglotz_deriv_im_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:07:50.214983+00:00
-- url     : https://prove2.me/theorems/ff418ac3-7584-418b-95c9-3ec0adee1b60
-- title:
--   Positive imaginary part of the derivative at the center of a Herglotz integral with sign-constrained boundary data
-- statement:
--   Let $R>0$ and let $u:\mathbb{C}\to\mathbb{R}$ be continuous on the circle $C_R=\{\zeta\in\mathbb{C}:|\zeta|=R\}$. Consider its Herglotz integral
--   $$\mathcal{H}_R[u](z)=\frac{1}{2\pi}\int_0^{2\pi}\frac{Re^{i\theta}+z}{Re^{i\theta}-z}\,u(Re^{i\theta})\,d\theta .$$
--   Assume that on the circle $u$ never has the same strict sign as the imaginary part, i.e. $u(\zeta)\,\operatorname{Im}\zeta\le0$ for all $\zeta\in C_R$, and that $u$ is strictly negative at the top point of the circle, $u(iR)<0$. Then the complex derivative of $\mathcal{H}_R[u]$ at the center has strictly positive imaginary part:
--
--   $$
--   \operatorname{Im}\,\mathcal{H}_R[u]'(0)>0 .
--   $$
--
--   In particular $\mathcal{H}_R[u]'(0)\neq0$. This nondegeneracy guarantees that a holomorphic function constructed by reflection through a Herglotz integral has nonzero derivative at the center of the disk.
--
--   **Formalization Note** $\mathcal{H}_R[u]$ is `herglotzExtension R u`, defined as Mathlib's `Real.circleAverage` over the circle of radius $R$ centred at $0$ of $\zeta\mapsto\frac{\zeta+z}{\zeta-z}\,u(\zeta)$, and $\mathcal{H}_R[u]'(0)$ is `deriv (herglotzExtension R u) 0`. The top point $iR$ is written `(R : ℂ) * Complex.I`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean#L90-L135

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.herglotz_deriv_im_pos {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R))
    (hn : ∀ z ∈ sphere 0 R, u z * z.im ≤ 0)
    (hp : u ((R : ℂ) * Complex.I) < 0) :
    0 < (deriv (herglotzExtension R u) 0).im := by sorry
