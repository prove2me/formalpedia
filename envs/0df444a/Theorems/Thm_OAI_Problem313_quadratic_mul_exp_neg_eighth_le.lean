-- Prove2me | Theorems.Thm_OAI_Problem313_quadratic_mul_exp_neg_eighth_le
-- name    : OAI.Problem313.quadratic_mul_exp_neg_eighth_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:13:03.39213+00:00
-- url     : https://prove2.me/theorems/752ef131-109f-4f30-b05f-abe17e22fa72
-- title:
--   A bound on $t^2e^{-t/8}$
-- statement:
--   For every real $t\ge0$,
--   $$
--   t^2e^{-t/8}\le256 .
--   $$
--
--   The exponentially small error of the capture argument is thereby dominated by an inverse-square term.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ExpQuadratic.lean#L9-L29

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

open OAI OAI.Problem313

theorem OAI.Problem313.quadratic_mul_exp_neg_eighth_le (t : ℝ) (ht : 0 ≤ t) :
    t ^ 2 * Real.exp (-t / 8) ≤ 256 := by sorry
