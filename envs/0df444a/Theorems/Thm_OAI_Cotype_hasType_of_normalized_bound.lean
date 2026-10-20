-- Prove2me | Theorems.Thm_OAI_Cotype_hasType_of_normalized_bound
-- name    : OAI.Cotype.hasType_of_normalized_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:20:40.121918+00:00
-- url     : https://prove2.me/theorems/7142167d-d722-4c49-8747-9429713042f1
-- title:
--   Type p from a bound on normalized families
-- statement:
--   Let $X$ be a real normed space, $1<p\le2$ and $D\ge0$. Suppose that for every $n$ and every $x_1,\dots,x_n\in X$ with $\sum_i\|x_i\|^p\le1$,
--   $$
--   \Bigl(\mathbb E_\varepsilon\Bigl\|\sum_i\varepsilon_ix_i\Bigr\|^2\Bigr)^{1/2}\le D .
--   $$
--   Then $X$ has type $p$: $(\mathbb E\|\sum_i\varepsilon_ix_i\|^2)^{1/2}\le D(\sum_i\|x_i\|^p)^{1/p}$ for all finite families.
--
--   It suffices to check the type inequality on the unit sphere of $\ell_p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/TypeExtrapolationParameters.lean#L67-L108

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
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem OAI.Cotype.hasType_of_normalized_bound {p D : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hD : 0 ≤ D)
    (h : ∀ (n : ℕ) (x : Fin n → X), (∑ i, ‖x i‖^p) ≤ 1 →
      cubeL2 X (rademacherSum X x) ≤ D) : HasType X p := by sorry
