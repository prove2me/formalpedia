-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedExtraction_equal_symbols_same_tag
-- name    : OAI.TreeEdit.BinaryLower.TaggedExtraction.equal_symbols_same_tag
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:21:32.842826+00:00
-- url     : https://prove2.me/theorems/da5fdf69-cdc9-4ca4-9913-535bca55ee53
-- title:
--   Equal letters of tagged row words have equal tags
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $X,Y$ be $T\times m$ arrays of blocks of width $B$ such that a letter occurring both in block $(a,i)$ of $X$ and in block $(b,j)$ of $Y$ forces $i=j$. If position $p$ of the row word of $X$ and position $q$ of the row word of $Y$ carry the same letter, then
--   $$
--   \lfloor p/B\rfloor\bmod m=\lfloor q/B\rfloor\bmod m .
--   $$
--
--   Disjoint child alphabets make every match respect the child index.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedExtraction.lean#L124-L145

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
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedExtraction
universe u
variable {α : Type u}

theorem OAI.TreeEdit.BinaryLower.TaggedExtraction.equal_symbols_same_tag {T m B : ℕ}
    (X Y : Fin T → Fin m → Word α B) (hm : 0 < m) (hB : 0 < B)
    (hdisjoint : ∀ (a b : Fin T) (i j : Fin m) (s : α),
      s ∈ (X a i).val → s ∈ (Y b j).val → i = j)
    (p q : ℕ) (hp : p < T * m * B) (hq : q < T * m * B)
    (heq : (rows X)[p]'(by rw [length_rows]; exact hp) =
      (rows Y)[q]'(by rw [length_rows]; exact hq)) :
    p / B % m = q / B % m := by sorry
