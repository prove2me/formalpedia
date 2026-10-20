-- Prove2me | Theorems.Thm_OAI_Cotype_rademacher_L2_le_four_L1
-- name    : OAI.Cotype.rademacher_L2_le_four_L1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:10:25.515243+00:00
-- url     : https://prove2.me/theorems/c79f6263-951f-4a11-89cd-b25002aa1068
-- title:
--   Kahane's inequality between L1 and L2 for Rademacher sums
-- statement:
--   Let $X$ be a real normed space and $x_1,\dots,x_n\in X$, with $S(\varepsilon)=\sum_i\varepsilon_ix_i$ for independent uniform signs $\varepsilon_i$. Then
--   $$
--   \bigl(\mathbb E\|S\|^2\bigr)^{1/2}\le4\,\mathbb E\|S\| .
--   $$
--
--   All moments of a vector Rademacher sum are comparable; here the constant for $L_2$ versus $L_1$ is $4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/RademacherComparison.lean#L72-L94

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.rademacher_L2_le_four_L1 {n : ℕ} (x : Fin n → X) :
    cubeL2 X (rademacherSum X x) ≤ 4 * average (fun u => ‖rademacherSum X x u‖) := by sorry
