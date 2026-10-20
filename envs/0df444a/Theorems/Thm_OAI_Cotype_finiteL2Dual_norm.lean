-- Prove2me | Theorems.Thm_OAI_Cotype_finiteL2Dual_norm
-- name    : OAI.Cotype.finiteL2Dual_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:15:18.427985+00:00
-- url     : https://prove2.me/theorems/9b04a94e-6719-43cb-990b-fcc08dec89a3
-- title:
--   The dual of a finite l2 sum is the l2 sum of duals
-- statement:
--   Let $X$ be a real normed space, $\Omega$ a finite set, and $g_a\in X^*$ for $a\in\Omega$. Let $\Gamma(z)=\sum_ag_a(z(a))$ on $\ell_2(\Omega;X)$. Then
--   $$
--   \|\Gamma\|=\Bigl(\sum_{a\in\Omega}\|g_a\|^2\Bigr)^{1/2}.
--   $$
--
--   So $\ell_2(\Omega;X)^*$ is isometric to $\ell_2(\Omega;X^*)$ for finite $\Omega$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FiniteL2DualNorm.lean#L13-L56

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
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem OAI.Cotype.finiteL2Dual_norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ = ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ := by sorry
