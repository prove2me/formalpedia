-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_choose_odd_lengths
-- name    : OAI.AsymptoticallyMinimalLittlewood.Packing.choose_odd_lengths
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:26:29.216463+00:00
-- url     : https://prove2.me/theorems/041bca65-fd05-4a86-9732-65774506b475
-- title:
--   Odd slot lengths whose shares of the period exceed twice prescribed weights
-- statement:
--   Let $J$ be a finite nonempty set and let $w:J\to\mathbb R$ satisfy $w_j>0$ for all $j\in J$ and $2\sum_{j\in J}w_j<1$. Then there exist natural numbers $d_j$ ($j\in J$) such that for every $i\in J$
--
--   $$
--   w_i<\frac{2d_i+1}{2\sum_{j\in J}(2d_j+1)} .
--   $$
--
--   Interpretation: put $L_j=2d_j+1$ (odd lengths) and $P=\sum_{j}L_j$. A period of length $P$ is divided into consecutive slots of lengths $L_j$, and the inequality says $2w_iP<L_i$, i.e. the share $L_i/P$ of slot $i$ in the period is more than twice the prescribed weight $w_i$. Odd lengths give every slot a well-defined central site. In the signed interval-packing construction this lemma converts the target arc widths $w_i$ into integer slot lengths.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Chunks.lean#L13-L41

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
universe uJ
open scoped BigOperators
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.Packing.choose_odd_lengths {J : Type uJ} [Fintype J] [Nonempty J]
    (w : J → ℝ) (hw : ∀ j, 0<w j) (hs : 2*∑ j, w j<1) :
    ∃ d : J → ℕ, ∀ i, w i < (2*(d i : ℝ)+1)/(2*∑ j, (2*(d j : ℝ)+1)) := by sorry
