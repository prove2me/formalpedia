-- Prove2me | Theorems.Thm_OAI_Problem313_permEdge_eq_self_of_not_touches
-- name    : OAI.Problem313.permEdge_eq_self_of_not_touches
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:00:34.799538+00:00
-- url     : https://prove2.me/theorems/c135cd4f-d743-49ba-a39a-61998f14f145
-- title:
--   Block permutations fix edges away from the block
-- statement:
--   Let $B$ be a set of vertices of $\{0,\dots,n-1\}$. A permutation $\pi$ is supported on $B$ if it fixes every vertex outside $B$, and an edge touches $B$ if it has an endpoint in $B$. The block orbit of an edge $e$ is $\{\pi(e):\pi\text{ supported on }B\}$. If $\pi$ is supported on $B$ and $e$ does not touch $B$, then
--   $$
--   \pi(e)=e .
--   $$
--
--   Permutations of a block act only on the edges touching it, so the exterior configuration is untouched.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockRestrictionSymmetry.lean#L53-L68

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

open OAI OAI.Problem313

theorem OAI.Problem313.permEdge_eq_self_of_not_touches {n : ℕ} {B : Finset (Fin n)}
    {π : Equiv.Perm (Fin n)} (hπ : SupportedOnBlock B π)
    (e : GraphEdge n) (he : ¬ EdgeTouches B e) : permEdge π e = e := by sorry
