-- Prove2me | Theorems.Thm_OAI_Cotype_geometric_block_bound
-- name    : OAI.Cotype.geometric_block_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:23:44.71131+00:00
-- url     : https://prove2.me/theorems/ba5a57f8-308d-4f1d-a083-6787cb031f88
-- title:
--   Rademacher bounds for one geometric block
-- statement:
--   Let $X$ be a real normed space, $A\ge0$, $r>0$, and $n,k\in\mathbb N$. Suppose
--   $$
--   \mathbb E\Bigl\|\sum_{i=1}^{n^{k+1}}\varepsilon_iy_i\Bigr\|^2\le A^{k+1}\sum_i\|y_i\|^2
--   $$
--   for all $y_1,\dots,y_{n^{k+1}}\in X$. Let $x_1,\dots,x_N$ vanish outside a set $s$ with $|s|\le n^{k+1}$, and satisfy $\|x_i\|\le r^{-k}$ on $s$. Then $(\mathbb E\|\sum_i\varepsilon_ix_i\|^2)^{1/2}\le\sqrt{An}\,(\sqrt{An}/r)^k$.
--
--   When $\sqrt{An}<r$ the blocks contribute a geometric series.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/GeometricTypeLevels.lean#L77-L105

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

theorem OAI.Cotype.geometric_block_bound {N n k : ℕ} {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r)
    (h : QuadraticTypeBound X (n^(k+1)) (A^(k+1)))
    (s : Finset (Fin N)) (hs : s.card ≤ n^(k+1))
    (x : Fin N → X) (hx0 : ∀ i, i ∉ s → x i = 0)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ (r⁻¹)^k) :
    cubeL2 X (rademacherSum X x) ≤
      Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by sorry
