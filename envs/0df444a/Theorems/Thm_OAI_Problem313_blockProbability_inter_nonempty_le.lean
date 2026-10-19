-- Prove2me | Theorems.Thm_OAI_Problem313_blockProbability_inter_nonempty_le
-- name    : OAI.Problem313.blockProbability_inter_nonempty_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:55:26.17177+00:00
-- url     : https://prove2.me/theorems/ef23d007-e182-4003-ae64-d103a3d977f4
-- title:
--   A random block rarely meets a small set
-- statement:
--   For a finite set $U$ and $m\in\mathbb{N}$, $\Pr_B$ denotes probability over a uniformly random $m$-element subset $B\subseteq U$. Let $E\subseteq U$ and $1\le m\le|U|$. Then
--   $$
--   \Pr_B\bigl[B\cap E\ne\emptyset\bigr]\le\frac{|E|\,m}{|U|} .
--   $$
--
--   A random block of size $m$ hits a fixed set with probability at most proportional to the set's size.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean#L227-L245

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

theorem OAI.Problem313.blockProbability_inter_nonempty_le (U E : Finset α) {m : ℕ}
    (hEU : E ⊆ U) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => (B ∩ E).Nonempty) ≤
      (E.card : ℝ) * m / U.card := by sorry
