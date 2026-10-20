-- Prove2me | Theorems.Thm_OAI_Cotype_geometric_level_card_le
-- name    : OAI.Cotype.geometric_level_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:22:04.634225+00:00
-- url     : https://prove2.me/theorems/84d92bb0-5455-49e3-b254-e58c73335aa2
-- title:
--   Few vectors of an lp-normalized family lie above a level
-- statement:
--   Let $X$ be a normed group, $n\ge1$, $p>0$ and $r>0$ with $r^p=n$. Let $x_1,\dots,x_N\in X$ satisfy $\sum_i\|x_i\|^p\le1$, and let $s$ be a set of indices with $\|x_i\|\ge r^{-(k+1)}$ for $i\in s$. Then
--   $$
--   |s|\le n^{k+1}.
--   $$
--
--   This is Chebyshev's counting bound for the $\ell_p$ mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/GeometricTypeLevels.lean#L55-L75

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

omit [NormedSpace ℝ X] in
theorem OAI.Cotype.geometric_level_card_le {N n k : ℕ} (hn : 0 < n) {p r : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hrp : r^p = n)
    (x : Fin N → X) (hx : (∑ i, ‖x i‖^p) ≤ 1)
    (s : Finset (Fin N)) (hs : ∀ i ∈ s, (r⁻¹)^(k+1) ≤ ‖x i‖) :
    s.card ≤ n^(k+1) := by sorry
