-- Prove2me | Theorems.Thm_OAI_Problem313_blockProbability_exists_le
-- name    : OAI.Problem313.blockProbability_exists_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:54:13.60597+00:00
-- url     : https://prove2.me/theorems/7513a788-ca55-4b54-9a7b-4d385dfc34bf
-- title:
--   Union bound for random fixed-size blocks
-- statement:
--   For a finite set $U$ and $m\in\mathbb{N}$, $\Pr_B$ denotes probability over a uniformly random $m$-element subset $B\subseteq U$. For a finite set $V$ and predicates $P_v$ ($v\in V$) on subsets,
--   $$
--   \Pr_B\bigl[\exists v\in V:\ P_v(B)\bigr]\le\sum_{v\in V}\Pr_B[P_v(B)] .
--   $$
--
--   This is the union bound for the uniform distribution on $m$-subsets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean#L138-L152

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
universe u
open Finset
variable {α : Type u} [DecidableEq α]

theorem OAI.Problem313.blockProbability_exists_le (U : Finset α) (m : ℕ)
    (V : Finset α) (P : α → Finset α → Prop) :
    blockProbability U m (fun B => ∃ v ∈ V, P v B) ≤
      ∑ v ∈ V, blockProbability U m (P v) := by sorry
