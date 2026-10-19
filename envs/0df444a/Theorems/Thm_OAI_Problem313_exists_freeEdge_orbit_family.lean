-- Prove2me | Theorems.Thm_OAI_Problem313_exists_freeEdge_orbit_family
-- name    : OAI.Problem313.exists_freeEdge_orbit_family
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:04:17.176357+00:00
-- url     : https://prove2.me/theorems/44b51927-281c-4e36-bfd6-ad05616efb25
-- title:
--   Each free edge has at least $|B|$ free orbit mates
-- statement:
--   Let $B$ be a set of vertices of $\{0,\dots,n-1\}$. A permutation $\pi$ is supported on $B$ if it fixes every vertex outside $B$, and an edge touches $B$ if it has an endpoint in $B$. The block orbit of an edge $e$ is $\{\pi(e):\pi\text{ supported on }B\}$. Let $|B|\ge3$ and let $e$ be an edge touching $B$. Then there is a set $S$ of edges touching $B$ with
--   $$
--   |S|\ge|B|,
--   $$
--   such that every $d\in S$ equals $\pi(e)$ for some permutation $\pi$ supported on $B$.
--
--   This is the form used for restrictions: the free coordinates are the edges touching the block, and the orbit mates are again free coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockOrbitSubtype.lean#L16-L36

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

theorem OAI.Problem313.exists_freeEdge_orbit_family {n : ℕ} (B : Finset (Fin n))
    (hB : 3 ≤ B.card) (e : {e : GraphEdge n // EdgeTouches B e}) :
    ∃ S : Finset {d : GraphEdge n // EdgeTouches B d},
      B.card ≤ S.card ∧ ∀ d ∈ S, ∃ π : Equiv.Perm (Fin n),
        SupportedOnBlock B π ∧ permEdge π e.val = d.val := by sorry
