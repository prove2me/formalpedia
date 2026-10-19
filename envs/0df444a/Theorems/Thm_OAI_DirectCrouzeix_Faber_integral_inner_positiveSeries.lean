-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_integral_inner_positiveSeries
-- name    : OAI.DirectCrouzeix.Faber.integral_inner_positiveSeries
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:50:19.723592+00:00
-- url     : https://prove2.me/theorems/4a421b8d-0f78-477e-ab08-3846bd1b4c8a
-- title:
--   Pairing a trigonometric polynomial with a continuous Hilbert-space-valued function through Fourier coefficients
-- statement:
--   Let $E$ be a complex Hilbert space whose inner product $\langle\cdot,\cdot\rangle$ is conjugate-linear in the first and linear in the second argument. Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its Haar probability measure $dt$, and for a continuous $f:\mathbb{T}\to E$ let
--   $$
--   \hat f(n)=\int_{\mathbb{T}}e^{-2\pi i n t}f(t)\,dt\in E\qquad(n\in\mathbb{Z})
--   $$
--   be its Fourier coefficients (Bochner integrals). For $N\in\mathbb{N}$ and vectors $C_0,\dots,C_{N-1}\in E$ consider the trigonometric polynomial with nonnegative frequencies
--   $$
--   P_C(t)=\sum_{k=0}^{N-1}e^{2\pi i k t}\,C_k .
--   $$
--   Then for every continuous $f:\mathbb{T}\to E$,
--   $$
--   \int_{\mathbb{T}}\big\langle P_C(t),f(t)\big\rangle\,dt=\sum_{k=0}^{N-1}\big\langle C_k,\hat f(k)\big\rangle .
--   $$
--
--   This is the vector-valued Parseval pairing between a trigonometric polynomial and a continuous function. With $f=P_C$ it yields $\int_{\mathbb{T}}\|P_C\|^2\,dt=\sum_k\|C_k\|^2$, and for $f$ whose Fourier coefficients of nonnegative index vanish it shows that $f$ is orthogonal to every such $P_C$; both consequences are used for energy identities of Faber series on the circle.
--
--   **Formalization Note** $P_C$ is `positiveSeries C` with `C : Fin N → E`, $e^{2\pi i k t}$ is Mathlib's `fourier k t` on `AddCircle (1:ℝ)` with `haarAddCircle`, $\hat f(k)$ is `fourierCoeff f k`, and the inner product is `inner ℂ`. The space $E$ is a complete complex inner product space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean#L133-L149

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_117 u_118 u_119 u_120 u_121 u_122 u_123 u_124 u_125 u_126 u_127 u_128
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
variable {E : Type u_127} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.DirectCrouzeix.Faber.integral_inner_positiveSeries {N : ℕ} (C : Fin N → E)
    (f : Angle → E) (hf : Continuous f) :
    (∫ t, inner ℂ (positiveSeries C t) (f t) ∂angularMeasure) =
      ∑ k, inner ℂ (C k) (fourierCoeff f (k:ℤ)) := by sorry
