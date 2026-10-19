-- Prove2me | Theorems.Thm_OAI_Problem313_weighted_holder_four_thirds
-- name    : OAI.Problem313.weighted_holder_four_thirds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:38:46.369155+00:00
-- url     : https://prove2.me/theorems/1337d5be-9a9f-4532-8752-58f84b1792aa
-- title:
--   Weighted Hölder inequality with exponents $4/3$ and $4$
-- statement:
--   Let $w\ge0$, $v$ and $u$ be real functions on a finite set. Then
--   $$
--   \Bigl|\sum_iw_iv_iu_i\Bigr|\le\Bigl(\sum_iw_i|v_i|^{4/3}\Bigr)^{3/4}\Bigl(\sum_iw_iu_i^4\Bigr)^{1/4} .
--   $$
--
--   The weights need not be normalized. This is the duality step that pairs a derivative with its low-degree projection.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ProjectionNorm.lean#L11-L58

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

theorem OAI.Problem313.weighted_holder_four_thirds {ι : Type u} [Fintype ι]
    (w v u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * v i * u i| ≤
      (∑ i, w i * |v i| ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) *
        (∑ i, w i * u i ^ 4) ^ (1 / 4 : ℝ) := by sorry
