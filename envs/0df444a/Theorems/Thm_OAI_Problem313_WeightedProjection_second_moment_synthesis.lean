-- Prove2me | Theorems.Thm_OAI_Problem313_WeightedProjection_second_moment_synthesis
-- name    : OAI.Problem313.WeightedProjection.second_moment_synthesis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:36:13.006197+00:00
-- url     : https://prove2.me/theorems/2f60c83e-9946-444a-875b-11c5bc33d845
-- title:
--   Parseval for a finite orthonormal expansion
-- statement:
--   Let $X$ be finite, $w$ a weight on $X$ and $(b_i)$ functions on $X$ that are orthonormal: $\sum_xw(x)b_i(x)b_j(x)=[i=j]$. For a finite index set $L$ and coefficients $c$, let $\Phi=\sum_{i\in L}c_ib_i$. Then
--   $$
--   \sum_xw(x)\Phi(x)^2=\sum_{i\in L}c_i^2 .
--   $$
--
--   The squared norm of a projection equals its coefficient energy. This is applied to low-level projections of Boolean functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/ProjectionIdentities.lean#L53-L71

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

open OAI OAI.Problem313 OAI.Problem313.WeightedProjection
universe u v
open scoped BigOperators
variable {ι : Type u} {X : Type v} [Fintype X]

theorem OAI.Problem313.WeightedProjection.second_moment_synthesis [DecidableEq ι]
    (w : X → ℝ) (basis : ι → X → ℝ)
    (horth : ∀ i j, (∑ x, w x * basis i x * basis j x) = if i = j then 1 else 0)
    (L : Finset ι) (c : ι → ℝ) :
    (∑ x, w x * (synthesis basis L c x) ^ 2) = ∑ i ∈ L, (c i) ^ 2 := by sorry
