-- Prove2me | Theorems.Thm_OAI_Problem313_SupportCombinatorics_exists_small_positive_degree
-- name    : OAI.Problem313.SupportCombinatorics.exists_small_positive_degree
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:51:38.80987+00:00
-- url     : https://prove2.me/theorems/ae52bed6-d38a-406b-b6b0-639447901c43
-- title:
--   A graph has a vertex of degree at most $\sqrt{2e}$
-- statement:
--   Let $S$ be a nonempty finite family of $2$-element sets (the edges of a graph). Then some vertex $u$ of $S$ has
--   $$
--   1\le\deg_S(u),\qquad\deg_S(u)^2\le2|S| .
--   $$
--
--   So every graph with $e$ edges has a non-isolated vertex of degree at most $\sqrt{2e}$. A random block meeting the support only at that vertex sees few edges.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SupportDegree.lean#L88-L108

import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree

open OAI OAI.Problem313 OAI.Problem313.SupportCombinatorics
universe u
open Finset
variable {α : Type u} [DecidableEq α]

theorem OAI.Problem313.SupportCombinatorics.exists_small_positive_degree {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) (hne : S.Nonempty) :
    ∃ u ∈ vertices S, 1 ≤ degree S u ∧ (degree S u)^2 ≤ 2 * S.card := by sorry
