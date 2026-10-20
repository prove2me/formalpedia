-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_split_rows_gap_bound
-- name    : OAI.TreeEdit.BinaryLower.Tagged.split_rows_gap_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:13:03.829252+00:00
-- url     : https://prove2.me/theorems/c8ac6806-ed8e-44b9-ad75-5bca5a07ed09
-- title:
--   Split rows force unmatched target positions
-- statement:
--   Words of length $TmB$ are read as $T$ rows of $m$ blocks of width $B$: position $t$ lies in block $\lfloor t/B\rfloor$, with tag $\lfloor t/B\rfloor\bmod m$ and row $\lfloor\lfloor t/B\rfloor/m\rfloor$. Let $u_0<\dots<u_n$ and $v_0<\dots<v_n$ (with $v_i<N$) be the matched positions of an alignment that respects tags, $\mathrm{tag}(u_i)=\mathrm{tag}(v_i)$, with $m\ge1$ and $B>0$. Then the number of split source rows satisfies
--   $$
--   |\mathrm{split}|\cdot(m-1)B\le N-(n+1).
--   $$
--
--   Each split row skips at least $(m-1)B$ target positions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean#L226-L256

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

theorem OAI.TreeEdit.BinaryLower.Tagged.split_rows_gap_bound {n N m B : ℕ} (hm : 1 ≤ m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hN : ∀ i, v i < N)
    (htags : ∀ i, (u i / B) % m = (v i / B) % m) :
    ((splitRows m B u v).card : ℝ) * (((m - 1) * B : ℕ) : ℝ) ≤
      (N : ℝ) - (n + 1) := by sorry
