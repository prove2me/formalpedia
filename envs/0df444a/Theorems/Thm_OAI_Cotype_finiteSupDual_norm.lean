-- Prove2me | Theorems.Thm_OAI_Cotype_finiteSupDual_norm
-- name    : OAI.Cotype.finiteSupDual_norm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:12:44.341208+00:00
-- url     : https://prove2.me/theorems/5de5b739-d5b2-4079-a190-bd5b1afcddca
-- title:
--   The dual norm of the finite sup-norm sum is the l1 sum
-- statement:
--   Let $X$ be a real normed space, $\Omega$ a finite set, and $g_a\in X^*$ for $a\in\Omega$. Equip $X^\Omega$ with the sup norm $\|f\|_\infty=\max_a\|f(a)\|$ and let $\Gamma(f)=\sum_ag_a(f(a))$. Then
--   $$
--   \|\Gamma\|=\sum_{a\in\Omega}\|g_a\| .
--   $$
--
--   So the natural embedding of $\ell_1(\Omega;X^*)$ into the dual of $\ell_\infty(\Omega;X)$ is isometric.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/FiniteSupDual.lean#L48-L68

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω]

theorem OAI.Cotype.finiteSupDual_norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteSupDual g‖ = ∑ a, ‖g a‖ := by sorry
