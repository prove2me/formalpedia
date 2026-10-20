-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_tagged_gap
-- name    : OAI.TreeEdit.BinaryLower.Tagged.tagged_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:11:28.432988+00:00
-- url     : https://prove2.me/theorems/86b258be-6f4a-4267-b185-5aeae4afd782
-- title:
--   Crossing a target row with matching tags costs a long gap
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $m\ge1$, $B>0$, and positions $a\le b$ in the same source row and $c,d$ with $c$ in an earlier target row than $d$. If the tags agree,
--   $$
--   \mathrm{tag}(a)=\mathrm{tag}(c),\qquad\mathrm{tag}(b)=\mathrm{tag}(d),
--   $$
--   then $d\ge c+1+(m-1)B$.
--
--   An alignment respecting tags cannot jump to the next row cheaply.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean#L58-L84

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset

theorem OAI.TreeEdit.BinaryLower.Tagged.tagged_gap {a b c d m B : ℕ} (hm : 1 ≤ m) (hB : 0 < B)
    (hab : a ≤ b) (hsource : a / B / m = b / B / m)
    (htarget : c / B / m < d / B / m)
    (htag₀ : (a / B) % m = (c / B) % m)
    (htag₁ : (b / B) % m = (d / B) % m) :
    c + 1 + (m - 1) * B ≤ d := by sorry
