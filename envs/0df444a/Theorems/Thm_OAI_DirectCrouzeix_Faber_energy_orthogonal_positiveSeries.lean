-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_energy_orthogonal_positiveSeries
-- name    : OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:51:14.005602+00:00
-- url     : https://prove2.me/theorems/c721a33d-8c28-43f2-a8f5-7b30f9c53b7a
-- title:
--   Energy splitting for a trigonometric polynomial plus a remainder with only negative frequencies
-- statement:
--   Let $E$ be a complex Hilbert space, let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its Haar probability measure $dt$, and for a continuous $r:\mathbb{T}\to E$ write $\hat r(j)=\int_{\mathbb{T}}e^{-2\pi i j t}\,r(t)\,dt$ $(j\in\mathbb{Z})$. For $N\in\mathbb{N}$ and $C_0,\dots,C_{N-1}\in E$ put
--   $$
--   P_C(t)=\sum_{k=0}^{N-1}e^{2\pi i k t}\,C_k .
--   $$
--   If $r:\mathbb{T}\to E$ is continuous and $\hat r(j)=0$ for every integer $j\ge0$, then
--   $$
--   \int_{\mathbb{T}}\big\|P_C(t)+r(t)\big\|^2\,dt=\sum_{k=0}^{N-1}\|C_k\|^2+\int_{\mathbb{T}}\|r(t)\|^2\,dt .
--   $$
--
--   Thus a continuous function whose spectrum lies in the negative frequencies is orthogonal in $L^2(\mathbb{T};E)$ to every trigonometric polynomial with nonnegative frequencies, and the energy of the sum splits as a Pythagorean identity in which the energy of $P_C$ is computed by Parseval. In the development $P_C$ is the main part and $r$ the remainder of a Faber series evaluated on the boundary circle, and the identity gives at once the lower bound of the Faber energy estimate.
--
--   **Formalization Note** $P_C$ is `positiveSeries C` with `C : Fin N → E`, $e^{2\pi i k t}$ is `fourier k t` on `AddCircle (1:ℝ)` with `haarAddCircle`, and $\hat r(j)$ is `fourierCoeff r j`. The vanishing hypothesis is stated for all integers $j\ge0$, although only $0\le j\le N-1$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/KernelContraction.lean#L162-L186

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

theorem OAI.DirectCrouzeix.Faber.energy_orthogonal_positiveSeries {N : ℕ} (C : Fin N → E)
    (r : Angle → E) (hr : Continuous r) (hfreq : ∀ j : ℤ, 0 ≤ j → fourierCoeff r j = 0) :
    (∫ t, ‖positiveSeries C t+r t‖^2 ∂angularMeasure) =
      (∑ k, ‖C k‖^2) + ∫ t, ‖r t‖^2 ∂angularMeasure := by sorry
