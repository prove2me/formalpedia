-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_tagged_slice_alignment
-- name    : OAI.TreeEdit.BinaryLower.Tagged.tagged_slice_alignment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:19:40.201057+00:00
-- url     : https://prove2.me/theorems/7aea1480-1cd2-4954-a2b6-14fcf67a946f
-- title:
--   Deficit lower bound for tagged row words
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $T\ge1$, $m\ge2$, $B>0$, and let $x,y$ be words of length $TmB$ in which equal letters occur only at positions with equal tags. Let $d\ge0$, and suppose every source row $a$ and target row $b$ satisfy
--   $$
--   \mathrm{lcs}(x_a,y_b)\le mB-d ,
--   $$
--   where $x_a,y_b$ are the rows as words of length $mB$. Then, with $g=(m-1)B$, the deficit satisfies
--   $$
--   r_{TmB}(x,y)\ge\frac{T\,d\,g}{d+g}.
--   $$
--
--   This is the row-level amplification step of the geometric induction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedAlignment.lean#L56-L105

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset

theorem OAI.TreeEdit.BinaryLower.Tagged.tagged_slice_alignment {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (x y : List α) (hx : x.length = T * m * B) (hy : y.length = T * m * B)
    (htags : ∀ p (hp : p < x.length) q (hq : q < y.length),
      x[p]'hp = y[q]'hq → p / B % m = q / B % m)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a < T, ∀ b < T,
      (lcs ((x.drop (a * (m * B))).take (m * B))
        ((y.drop (b * (m * B))).take (m * B)) : ℝ) ≤ (m * B : ℕ) - d) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ)) ≤
      (deficit (T * m * B) x y : ℝ) := by sorry
