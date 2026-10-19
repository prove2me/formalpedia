-- Prove2me | Theorems.Thm_OAI_Problem313_blockProbability_singleton_inter_ge
-- name    : OAI.Problem313.blockProbability_singleton_inter_ge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:54:50.857915+00:00
-- url     : https://prove2.me/theorems/c712caac-b965-4a9c-8025-97c42b124a7a
-- title:
--   A random block meets a set in exactly one given point
-- statement:
--   For a finite set $U$ and $m\in\mathbb{N}$, $\Pr_B$ denotes probability over a uniformly random $m$-element subset $B\subseteq U$. Let $u\in V\subseteq U$ and $2\le m\le|U|$. Then
--   $$
--   \Pr_B\bigl[B\cap V=\{u\}\bigr]\ge\frac m{|U|}\Bigl(1-\frac{(|V|-1)(m-1)}{|U|-1}\Bigr) .
--   $$
--
--   When $|V|m\ll|U|$, a random block containing $u$ typically avoids the rest of $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean#L195-L225

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

theorem OAI.Problem313.blockProbability_singleton_inter_ge (U V : Finset α) {m : ℕ} {u : α}
    (hVU : V ⊆ U) (hu : u ∈ V) (hm : 2 ≤ m) (hmn : m ≤ U.card) :
    (m : ℝ) / U.card *
        (1 - ((V.card : ℝ) - 1) * ((m : ℝ) - 1) / ((U.card : ℝ) - 1)) ≤
      blockProbability U m (fun B => B ∩ V = {u}) := by sorry
