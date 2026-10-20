-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedNonsplit_natRowCount_div_le_width
-- name    : OAI.TreeEdit.BinaryLower.TaggedNonsplit.natRowCount_div_le_width
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:14:39.228118+00:00
-- url     : https://prove2.me/theorems/2a8f85d4-7683-4321-be42-594ad397a718
-- title:
--   An injective sequence has at most W values in each window of width W
-- statement:
--   Let $u:\{1..N\}\to\mathbb N$ be injective, $W>0$ and $r\in\mathbb N$. Then
--   $$
--   \bigl|\{i:\ \lfloor u_i/W\rfloor=r\}\bigr|\le W .
--   $$
--
--   At most $W$ distinct naturals lie in $[rW,(r+1)W)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean#L197-L218

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedNonsplit
open scoped BigOperators

theorem OAI.TreeEdit.BinaryLower.TaggedNonsplit.natRowCount_div_le_width {N : ℕ}
    (u : Fin N → ℕ) (hu : Function.Injective u) (W : ℕ) (hW : 0 < W) (r : ℕ) :
    natRowCount (fun i => u i / W) r ≤ W := by sorry
