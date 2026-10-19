-- Prove2me | Theorems.Thm_OAI_Problem313_block_filter_eq_vertex_filter
-- name    : OAI.Problem313.block_filter_eq_vertex_filter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:53:20.93989+00:00
-- url     : https://prove2.me/theorems/321a3a68-9e35-45ac-a6a3-adc2d87052f9
-- title:
--   A block meeting the support in one vertex sees exactly its edges
-- statement:
--   Let $S$ be a set of graph edges on $\{0,\dots,n-1\}$, $B$ a vertex set and $u$ a vertex. If $B$ meets the vertex set of $S$ exactly in $u$, i.e. $B\cap\bigcup_{e\in S}e=\{u\}$, then
--   $$
--   \{e\in S:\ e\cap B\ne\emptyset\}=\{e\in S:\ u\in e\} .
--   $$
--
--   Restricting to such a block keeps precisely the support edges at $u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockIncidence.lean#L9-L31

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree

open OAI OAI.Problem313

theorem OAI.Problem313.block_filter_eq_vertex_filter {n : ℕ}
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) (u : Fin n)
    (h : B ∩ S.biUnion (fun e => e.val) = {u}) :
    S.filter (fun e => (e.val ∩ B).Nonempty) =
      S.filter (fun e => u ∈ e.val) := by sorry
