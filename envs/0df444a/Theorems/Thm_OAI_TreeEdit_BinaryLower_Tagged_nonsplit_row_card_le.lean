-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_nonsplit_row_card_le
-- name    : OAI.TreeEdit.BinaryLower.Tagged.nonsplit_row_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:12:26.872978+00:00
-- url     : https://prove2.me/theorems/7a3ee4fc-248a-4edb-9f27-27882ff04acd
-- title:
--   A nonsplit row obeys the local matching bound
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $u$ (monotone) and $v$ (below $TmB$) give the matched positions of an alignment, and $d\le mB$. Suppose every pair of rows $(a,b)$ receives at most $mB-d$ matches from source row $a$ to target row $b$. If source row $a<T$ is not split, i.e. no consecutive matches in row $a$ cross a target row boundary, then
--   $$
--   \bigl|\{i:\ u_i\text{ in row }a\}\bigr|\le mB-d .
--   $$
--
--   A row that is not split behaves like a single row-to-row comparison.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean#L194-L224

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

theorem OAI.TreeEdit.BinaryLower.Tagged.nonsplit_row_card_le {n T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : Monotone u)
    (hv : ∀ i, v i < T * m * B) (d : ℝ) (hd : d ≤ (m * B : ℕ))
    (hlocal : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin (n + 1) =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d)
    {a : ℕ} (ha : a < T) (haS : a ∉ splitRows m B u v) :
    ((univ.filter fun i : Fin (n + 1) => u i / B / m = a).card : ℝ) ≤
      (m * B : ℕ) - d := by sorry
