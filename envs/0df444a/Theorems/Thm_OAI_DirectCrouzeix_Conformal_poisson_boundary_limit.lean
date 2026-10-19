-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_poisson_boundary_limit
-- name    : OAI.DirectCrouzeix.Conformal.poisson_boundary_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:02:29.824057+00:00
-- url     : https://prove2.me/theorems/11fd499f-84aa-4b99-814e-b357b7c2bb6e
-- title:
--   Boundary continuity of the Poisson integral on a disk
-- statement:
--   Let $R>0$ and let $u:\mathbb{C}\to\mathbb{R}$ be continuous on the circle $C_R=\{\zeta\in\mathbb{C}:|\zeta|=R\}$. The Poisson extension of $u$ is
--   $$P_R[u](z)=\frac{1}{2\pi}\int_0^{2\pi}\frac{R^2-|z|^2}{|Re^{i\theta}-z|^2}\,u(Re^{i\theta})\,d\theta .$$
--   Then for every $p\in C_R$, the Poisson extension tends to the boundary value $u(p)$ as $z$ approaches $p$ from inside the open disk $B(0,R)=\{z:|z|<R\}$:
--
--   $$
--   \lim_{\substack{z\to p\\ |z|<R}}P_R[u](z)=u(p) .
--   $$
--
--   This is the boundary half of the solution of the Dirichlet problem on a disk: together with the harmonicity of $P_R[u]$ in $B(0,R)$, it shows that the function equal to $P_R[u]$ in the open disk and to $u$ on $C_R$ is continuous on the closed disk. In this development it is what allows a harmonic function to be compared with a Poisson integral by the maximum principle.
--
--   **Formalization Note** $P_R[u]$ is `poissonExtension R u`, defined for every $z\in\mathbb{C}$ as Mathlib's `Real.circleAverage` over the circle of radius $R$ centred at $0$ of $\zeta\mapsto P(z,\zeta)\,u(\zeta)$, where $P(z,\zeta)=(|\zeta|^2-|z|^2)/|\zeta-z|^2$ is `poissonKernel 0 z ζ`. Only points $z$ of the open disk enter the statement, and for them the integrand is continuous on the circle. The limit is along the neighbourhood filter of $p$ restricted to `ball 0 R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean#L55-L149

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.poisson_boundary_limit {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : ContinuousOn u (sphere 0 R)) {p : ℂ} (hp : p ∈ sphere 0 R) :
    Tendsto (poissonExtension R u) (𝓝[ball 0 R] p) (𝓝 (u p)) := by sorry
