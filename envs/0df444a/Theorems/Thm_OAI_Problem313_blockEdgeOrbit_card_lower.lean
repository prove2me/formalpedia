-- Prove2me | Theorems.Thm_OAI_Problem313_blockEdgeOrbit_card_lower
-- name    : OAI.Problem313.blockEdgeOrbit_card_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:03:38.386992+00:00
-- url     : https://prove2.me/theorems/31abb490-838f-4cd5-aafd-e29fecd89e69
-- title:
--   Edges meeting a block have block orbits of size at least $|B|$
-- statement:
--   Let $B$ be a set of vertices of $\{0,\dots,n-1\}$. A permutation $\pi$ is supported on $B$ if it fixes every vertex outside $B$, and an edge touches $B$ if it has an endpoint in $B$. The block orbit of an edge $e$ is $\{\pi(e):\pi\text{ supported on }B\}$. If $|B|\ge3$ and the edge $e$ meets $B$, then
--   $$
--   |\text{block orbit of }e|\ge|B| .
--   $$
--
--   For a vertex-invariant property, every edge touching the block has many equally influential orbit mates. This bounds its influence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean#L143-L170

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

open OAI OAI.Problem313
universe u

theorem OAI.Problem313.blockEdgeOrbit_card_lower {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} (hB : 3 ≤ B.card) (hmeet : (e.val ∩ B).Nonempty) :
    B.card ≤ (blockEdgeOrbit B e).card := by sorry
