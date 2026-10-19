-- Prove2me | Theorems.Thm_OAI_Problem313_weighted_projection_noise_bound
-- name    : OAI.Problem313.weighted_projection_noise_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:40:57.262421+00:00
-- url     : https://prove2.me/theorems/c5e21713-7370-476c-9c50-d779178fc238
-- title:
--   Energy of a projection of a ternary function
-- statement:
--   Let $w\ge0$ on a finite set, $v$ with values in $\{-1,0,1\}$, $u$ real, and $\rho,d$ with $\rho\ge0$. Suppose
--   $$
--   \sum_iw_iv_iu_i=\sum_iw_iu_i^2,\qquad\sum_iw_iu_i^4\le\rho^{-4d}\Bigl(\sum_iw_iu_i^2\Bigr)^2 .
--   $$
--   Then $\sum_iw_iu_i^2\le\rho^{-2d}\bigl(\sum_{i:v_i\ne0}w_i\bigr)^{3/2}$.
--
--   With $u$ the low-degree projection of a derivative $v=\Delta_if$, the energy of the projection is bounded by the influence to the power $3/2$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ProjectionNorm.lean#L129-L149

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities

open OAI OAI.Problem313
universe u
open scoped BigOperators

theorem OAI.Problem313.weighted_projection_noise_bound {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hv : ∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1)
    (ρ d : ℝ) (hρ : 0 ≤ ρ)
    (hproj : (∑ i, w i * v i * u i) = ∑ i, w i * u i ^ 2)
    (hfour : (∑ i, w i * u i ^ 4) ≤
      ρ ^ (-4 * d) * (∑ i, w i * u i ^ 2) ^ 2) :
    (∑ i, w i * u i ^ 2) ≤
      ρ ^ (-2 * d) * (∑ i, if v i ≠ 0 then w i else 0) ^ (3 / 2 : ℝ) := by sorry
