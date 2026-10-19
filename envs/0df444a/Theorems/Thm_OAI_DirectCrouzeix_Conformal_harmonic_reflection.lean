-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Conformal_harmonic_reflection
-- name    : OAI.DirectCrouzeix.Conformal.harmonic_reflection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:05:48.664054+00:00
-- url     : https://prove2.me/theorems/a3fed5e8-78e2-46b1-a9d3-7638bb9e36a1
-- title:
--   Harmonic reflection: the Herglotz integral of the odd reflection recovers a harmonic function on the upper half-disk
-- statement:
--   Let $R>0$ and write
--   $$D_R^+=\{z\in\mathbb{C}:\ |z|<R,\ \operatorname{Im}z>0\},\qquad K_R^+=\{z\in\mathbb{C}:\ |z|\le R,\ \operatorname{Im}z\ge0\}$$
--   for the open and the closed upper half-disk. Let $u:\mathbb{C}\to\mathbb{R}$ be harmonic on $D_R^+$, continuous on $K_R^+$, and zero on the real axis ($u(z)=0$ whenever $\operatorname{Im}z=0$). Let $\tilde u$ be the odd reflection of $u$, i.e. $\tilde u(z)=u(z)$ if $\operatorname{Im}z\ge0$ and $\tilde u(z)=-u(\bar z)$ if $\operatorname{Im}z<0$, and let
--   $$\mathcal{H}_R[\tilde u](z)=\frac{1}{2\pi}\int_0^{2\pi}\frac{Re^{i\theta}+z}{Re^{i\theta}-z}\,\tilde u(Re^{i\theta})\,d\theta$$
--   be its Herglotz integral over the circle of radius $R$. Then the real part of this integral reproduces $u$ on the upper half-disk:
--
--   $$
--   \operatorname{Re}\mathcal{H}_R[\tilde u](z)=u(z)\qquad\text{for all } z\in D_R^+ .
--   $$
--
--   Since the Herglotz integral of continuous boundary data is holomorphic on the whole open disk $\{|z|<R\}$, the theorem exhibits $u$ on $D_R^+$ as the real part of a holomorphic function on the full disk. This is a constructive form of the Schwarz reflection principle for harmonic functions vanishing on a diameter; in this development it is applied to $\log|f|$ for holomorphic functions $f$ whose modulus tends to $1$ on a segment.
--
--   **Formalization Note** $\mathcal{H}_R[\tilde u]$ is `herglotzExtension R (oddUpper u)`, defined as Mathlib's `Real.circleAverage` over the circle of radius $R$ centred at $0$ of $\zeta\mapsto\frac{\zeta+z}{\zeta-z}\,\tilde u(\zeta)$ (the kernel is `herglotzRieszKernel 0 z ζ`). Harmonicity is `HarmonicOnNhd u (upperBall R)`: near every point of $D_R^+$, $u$ is $C^2$ with vanishing Laplacian. The sets $D_R^+$ and $K_R^+$ are `upperBall R` and `upperClosedBall R`. The vanishing hypothesis is assumed on the whole real axis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean#L155-L200

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

theorem OAI.DirectCrouzeix.Conformal.harmonic_reflection {R : ℝ} (hR : 0 < R) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u (upperBall R))
    (huc : ContinuousOn u (upperClosedBall R))
    (hzero : ∀ z, z.im = 0 → u z = 0) :
    EqOn (fun z => (herglotzExtension R (oddUpper u) z).re) u (upperBall R) := by sorry
