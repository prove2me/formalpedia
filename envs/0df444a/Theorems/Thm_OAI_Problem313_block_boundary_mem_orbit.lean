-- Prove2me | Theorems.Thm_OAI_Problem313_block_boundary_mem_orbit
-- name    : OAI.Problem313.block_boundary_mem_orbit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:02:50.751482+00:00
-- url     : https://prove2.me/theorems/2d40360c-3b03-4d72-b84b-0b7dbcb20e37
-- title:
--   Boundary edges with a common exterior endpoint form one orbit
-- statement:
--   Let $B$ be a set of vertices of $\{0,\dots,n-1\}$. A permutation $\pi$ is supported on $B$ if it fixes every vertex outside $B$, and an edge touches $B$ if it has an endpoint in $B$. The block orbit of an edge $e$ is $\{\pi(e):\pi\text{ supported on }B\}$. Let $e=\{u,w\}$ with $u\in B$ and $w\notin B$. Then for every $v\in B$,
--   $$
--   \{v,w\}\in\text{block orbit of }e .
--   $$
--
--   So the block orbit of a boundary edge contains at least $|B|$ edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean#L112-L128

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

theorem OAI.Problem313.block_boundary_mem_orbit {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} {u w : Fin n} (hu : u ∈ B) (hw : w ∉ B)
    (he : e.val = {u, w}) (v : B) :
    blockBoundaryEdge w hw v ∈ blockEdgeOrbit B e := by sorry
