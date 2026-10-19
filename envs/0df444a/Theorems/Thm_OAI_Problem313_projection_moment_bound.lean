-- Prove2me | Theorems.Thm_OAI_Problem313_projection_moment_bound
-- name    : OAI.Problem313.projection_moment_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:39:47.129365+00:00
-- url     : https://prove2.me/theorems/ffba6399-ab51-465a-b7fe-9ba1497a98dc
-- title:
--   Scalar cancellation in the $L^4$ duality argument
-- statement:
--   Let $M,V,H,A\ge0$ with
--   $$
--   M\le V^{3/4}H^{1/4},\qquad H\le A^4M^2 .
--   $$
--   Then $M\le A^2V^{3/2}$.
--
--   Here $M$ is the energy of a projection, $V$ the measure of the support of the function, and $H$ the fourth moment of the projection. Combining Hölder with hypercontractivity yields the Talagrand-type $3/2$ power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ProjectionNorm.lean#L60-L90

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

theorem OAI.Problem313.projection_moment_bound {M V H A : ℝ}
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hdual : M ≤ V ^ (3 / 4 : ℝ) * H ^ (1 / 4 : ℝ))
    (hfour : H ≤ A ^ 4 * M ^ 2) :
    M ≤ A ^ 2 * V ^ (3 / 2 : ℝ) := by sorry
