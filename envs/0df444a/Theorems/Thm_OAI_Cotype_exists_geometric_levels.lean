-- Prove2me | Theorems.Thm_OAI_Cotype_exists_geometric_levels
-- name    : OAI.Cotype.exists_geometric_levels
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:21:20.27662+00:00
-- url     : https://prove2.me/theorems/58c5cb4a-c498-47f1-9627-b7abe8fa3029
-- title:
--   Assigning geometric levels to vectors in the unit ball
-- statement:
--   Let $X$ be a normed group, $r>1$, and $x_1,\dots,x_N\in X$ with $\|x_i\|\le1$. There are levels $l_1,\dots,l_N\in\mathbb N$ such that for every $i$,
--   $$
--   \|x_i\|\le r^{-l_i},\qquad\text{and}\qquad r^{-(l_i+1)}<\|x_i\|\ \text{ if }x_i\ne0 .
--   $$
--
--   Each nonzero vector lies in exactly one dyadic-type shell $(r^{-(l+1)},r^{-l}]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/GeometricTypeLevels.lean#L19-L47

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
theorem OAI.Cotype.exists_geometric_levels {N : ℕ} {r : ℝ} (hr : 1 < r)
    (x : Fin N → X) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃ l : Fin N → ℕ, ∀ i, ‖x i‖ ≤ (r⁻¹)^(l i) ∧
      (x i ≠ 0 → (r⁻¹)^(l i+1) < ‖x i‖) := by sorry
