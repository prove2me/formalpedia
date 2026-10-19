-- Prove2me | Theorems.Thm_OAI_Problem313_support_vertices_card_le
-- name    : OAI.Problem313.support_vertices_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:56:09.310087+00:00
-- url     : https://prove2.me/theorems/46016ec8-fd72-4513-94e4-e411d969b9aa
-- title:
--   An edge set has at most twice as many vertices as edges
-- statement:
--   For a finite set $S$ of graph edges on $\{0,\dots,n-1\}$,
--   $$
--   \Bigl|\bigcup_{e\in S}e\Bigr|\le2|S| .
--   $$
--
--   The vertex support of a Fourier coefficient is at most twice its degree. This bounds collisions with random blocks.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SupportDegreeGraph.lean#L10-L22

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting

open OAI OAI.Problem313
open Finset

theorem OAI.Problem313.support_vertices_card_le {n : ℕ} (S : Finset (GraphEdge n)) :
    (S.biUnion (fun e => e.val)).card ≤ 2 * S.card := by sorry
