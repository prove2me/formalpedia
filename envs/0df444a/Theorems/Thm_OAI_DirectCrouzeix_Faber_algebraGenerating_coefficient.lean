-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_algebraGenerating_coefficient
-- name    : OAI.DirectCrouzeix.Faber.algebraGenerating_coefficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:52:33.675313+00:00
-- url     : https://prove2.me/theorems/decb824b-d68e-4c76-8c3d-649f7300b98a
-- title:
--   Taylor coefficients of the Banach-algebra Faber generating function are the Faber polynomials $F_k(A)$
-- statement:
--   Let $\mathcal{A}$ be a complex Banach algebra with unit $\mathbf 1$. Let $c\in\mathbb{C}$ with $c\neq0$ and let $g:\mathbb{C}\to\mathbb{C}$ be analytic at $0$. With $L(u)=\big(c+u\,g(u)\big)^{-1}$, $W(u)=u\,L(u)$ and $V(u)=\big(c-u^2g'(u)\big)L(u)$, define for $k\in\mathbb{N}$ the Faber polynomials
--   $$
--   F_k(z)=\sum_{j=0}^{k}a_{k,j}\,z^j,\qquad a_{k,j}=\frac{1}{k!}\,\frac{d^k}{du^k}\Big|_{u=0}\Big(V(u)\,W(u)^j\Big).
--   $$
--   For $A\in\mathcal{A}$ consider the $\mathcal{A}$-valued generating function
--   $$
--   G_A(u)=\big(c-u^2g'(u)\big)\Big(\big(c+u\,g(u)\big)\mathbf 1-u\,A\Big)^{-1},
--   $$
--   the inverse being taken in $\mathcal{A}$; it exists for $u$ near $0$, because the bracket equals $c\,\mathbf 1$ at $u=0$. Then for every $k\in\mathbb{N}$,
--   $$
--   \frac{1}{k!}\,G_A^{(k)}(0)=F_k(A)=\sum_{j=0}^{k}a_{k,j}\,A^j .
--   $$
--
--   In other words $G_A(u)=\sum_{k\ge0}F_k(A)\,u^k$ near $u=0$: the scalar generating function $\frac{c-u^2g'(u)}{c+u(g(u)-z)}$ of the Faber polynomials of $\Phi(\zeta)=c\zeta+g(1/\zeta)$ remains valid when $z$ is replaced by an arbitrary element $A$ of a Banach algebra. This is the bridge from the scalar Faber theory to Faber polynomials of matrices and operators, and it is the input for the Fourier representation of $F_k(A)$ on the unit circle.
--
--   **Formalization Note** $G_A$ is `algebraGenerating c g A`, defined with `Ring.inverse` of `algebraDenominator c g A u` $=(c+u\,g(u))\mathbf 1-uA$; `Ring.inverse` returns $0$ at non-invertible elements, a convention that plays no role near $u=0$. The Taylor coefficient is `taylorCoeff`, i.e. $k!^{-1}$ times Lean's `iteratedDeriv k` at $0$, $F_k$ is `faberBasis c g k`, and $F_k(A)$ is `Polynomial.aeval A`. The algebra is a `NormedRing` with a `NormedAlgebra` structure over the complex numbers and is complete; $g'$ is Lean's `deriv g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberCalculus.lean#L94-L137

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_129 u_130
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem OAI.DirectCrouzeix.Faber.algebraGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (A : 𝔄) (k : ℕ) :
    taylorCoeff (algebraGenerating c g A) k = Polynomial.aeval A (faberBasis c g k) := by sorry
