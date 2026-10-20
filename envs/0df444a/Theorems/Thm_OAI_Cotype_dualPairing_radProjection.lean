-- Prove2me | Theorems.Thm_OAI_Cotype_dualPairing_radProjection
-- name    : OAI.Cotype.dualPairing_radProjection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:16:38.842977+00:00
-- url     : https://prove2.me/theorems/d45a0359-82d1-4031-afe9-0fcd2333b49e
-- title:
--   The Rademacher projection is self-adjoint
-- statement:
--   Let $X$ be a real normed space, $f:\{0,1\}^n\to X$ and $g:\{0,1\}^n\to X^*$. Let $\mathrm{Rad}$ be the Rademacher projection $\mathrm{Rad}\,f(u)=\sum_i\varepsilon_i(u)\hat f_i$, with $\hat f_i=\mathbb E_v\varepsilon_i(v)f(v)$, and $\langle f,g\rangle=\mathbb E_u\,g(u)(f(u))$. Then
--   $$
--   \langle f,\mathrm{Rad}\,g\rangle=\langle\mathrm{Rad}\,f,g\rangle .
--   $$
--
--   This duality is why K-convexity of $X$ transfers to $X^*$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/KConvexDuality.lean#L40-L53

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification

open OAI OAI.Cotype
open scoped BigOperators
open WithLp
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.dualPairing_radProjection {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    dualPairing f (radProjection (X →L[ℝ] ℝ) g) = dualPairing (radProjection X f) g := by sorry
