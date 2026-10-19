-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_oddUpper_continuous_circle
-- name    : OAI.DirectCrouzeix.Conformal.oddUpper_continuous_circle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:04:16.040991+00:00
-- url     : https://prove2.me/theorems/3ed6624e-6596-4e09-a5ab-2790e6cd35ed
-- title:
--   Continuity on a circle of the odd reflection of a function vanishing on the real axis
-- statement:
--   Let $R\in\mathbb{R}$ and let $u:\mathbb{C}\to\mathbb{R}$ be continuous on the closed upper half-disk
--   $$K_R^+=\{z\in\mathbb{C}:\ |z|\le R,\ \operatorname{Im}z\ge0\},$$
--   and suppose that $u$ vanishes on the real axis: $u(z)=0$ for every $z\in\mathbb{C}$ with $\operatorname{Im}z=0$. Define the odd reflection of $u$ across the real axis by
--   $$\tilde u(z)=\begin{cases}u(z), & \operatorname{Im}z\ge0,\\ -u(\bar z), & \operatorname{Im}z<0.\end{cases}$$
--   Then $\tilde u$ is continuous on the circle $C_R=\{z\in\mathbb{C}:|z|=R\}$, in the sense that its restriction to $C_R$ is continuous:
--
--   $$
--   \lim_{\substack{w\to z\\ |w|=R}}\tilde u(w)=\tilde u(z)\qquad\text{for every } z\in\mathbb{C} \text{ with } |z|=R .
--   $$
--
--   Under the vanishing hypothesis the reflected function is odd under conjugation, $\tilde u(\bar z)=-\tilde u(z)$. The lemma makes $\tilde u$ admissible continuous boundary data for the Poisson and Herglotz integrals over $C_R$, which is the starting point of the Schwarz reflection principle for harmonic functions vanishing on a diameter.
--
--   **Formalization Note** The odd reflection is `oddUpper u`, $K_R^+$ is `upperClosedBall R`, and the conclusion is `ContinuousOn (oddUpper u) (sphere 0 R)`. No sign condition is imposed on $R$: for $R<0$ the circle is empty, and for $R=0$ it is the single point $0$. The vanishing hypothesis is assumed on the whole real axis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean#L129-L153

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Conformal
universe u_132
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
open Filter Metric Set
open scoped Topology ComplexConjugate
open Function Complex
open scoped Pointwise
open InnerProductSpace Real

theorem OAI.DirectCrouzeix.Conformal.oddUpper_continuous_circle {R : ℝ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    ContinuousOn (oddUpper u) (sphere 0 R) := by sorry
