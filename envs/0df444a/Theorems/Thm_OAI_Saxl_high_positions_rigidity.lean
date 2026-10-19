-- Prove2me | Theorems.Thm_OAI_Saxl_high_positions_rigidity
-- name    : OAI.Saxl.high_positions_rigidity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:58:39.752528+00:00
-- url     : https://prove2.me/theorems/4e5f97a3-8da6-4693-93b2-6d2e289cdb75
-- title:
--   Rigidity of high cells under row- and column-preserving permutations of a staircase
-- statement:
--   Let $h,s\in\mathbb{N}$ and let $\delta_{h+s}=\{(i,j)\in\mathbb{N}^2: i+j<h+s\}$ be the staircase diagram, whose cells $x=(i,j)$ have row $\operatorname{row}(x)=i$ and column $\operatorname{col}(x)=j$. Let $g$ and $k$ be permutations of the cells of $\delta_{h+s}$ such that $g$ preserves rows and $k$ preserves columns,
--   $$\operatorname{row}(g(x))=\operatorname{row}(x),\qquad\operatorname{col}(k(x))=\operatorname{col}(x)\qquad\text{for all cells }x,$$
--   and suppose that, for every cell $x$, $g$ moves $x$ into a column with index at least $s$ exactly when $k$ moves $x$ into a row with index at least $s$:
--   $$s\le\operatorname{col}(g(x))\iff s\le\operatorname{row}(k(x)).$$
--   Then for every cell $x=(i,j)$ of $\delta_{h+s}$,
--   $$s\le\operatorname{col}(g(x))\iff i+j<h .$$
--
--   In words, the set of cells that $g$ sends to the high columns (and $k$ to the high rows) is exactly the smaller staircase $\delta_h$ in the top-left corner. This is applied to the staircase tensor $e_{T'}\otimes e_T$ after projecting onto pair-words whose two letters are both at least $s$ or both below $s$: in every word that survives, the positions carrying letters at least $s$ are exactly the positions whose cell lies in $\delta_h$.
--
--   **Formalization Note** The cells are elements of `(staircase (h+s)).cells`, with `x.val.1` the row and `x.val.2` the column; $g$ and $k$ have type `Equiv.Perm (staircase (h+s)).cells`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HighProjection.lean#L43-L93

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection

open OAI OAI.Saxl
open scoped TensorProduct

theorem OAI.Saxl.high_positions_rigidity (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by sorry
