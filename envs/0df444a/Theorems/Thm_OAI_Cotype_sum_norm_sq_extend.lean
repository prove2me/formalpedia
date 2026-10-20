-- Prove2me | Theorems.Thm_OAI_Cotype_sum_norm_sq_extend
-- name    : OAI.Cotype.sum_norm_sq_extend
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:08:54.801368+00:00
-- url     : https://prove2.me/theorems/77967b91-a917-4951-afb0-5eda73600c8b
-- title:
--   Extending a vector family by zero keeps its square sum
-- statement:
--   Let $X$ be a normed group, $j:\{1,\dots,n\}\to\{1,\dots,m\}$ injective, and $x_1,\dots,x_n\in X$. Let $\tilde x$ be the extension of $x$ along $j$ by zero: $\tilde x_{j(i)}=x_i$ and $\tilde x_u=0$ off the image of $j$. Then
--   $$
--   \sum_{u=1}^m\|\tilde x_u\|^2=\sum_{i=1}^n\|x_i\|^2 .
--   $$
--
--   Padding by zero vectors does not change the quadratic size of a family.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/IndependentSigns.lean#L45-L58

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

omit [NormedSpace ℝ X] in
theorem OAI.Cotype.sum_norm_sq_extend {n m : ℕ} (j : Fin n ↪ Fin m) (x : Fin n → X) :
    (∑ u, ‖Function.extend j x (fun _ => 0) u‖^2) = ∑ i, ‖x i‖^2 := by sorry
