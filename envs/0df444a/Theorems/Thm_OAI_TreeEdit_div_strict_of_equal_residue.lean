-- Prove2me | Theorems.Thm_OAI_TreeEdit_div_strict_of_equal_residue
-- name    : OAI.TreeEdit.div_strict_of_equal_residue
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:16:52.648717+00:00
-- url     : https://prove2.me/theorems/aa456c3b-7b19-4cfb-ae73-e9be8e623631
-- title:
--   Strictly increasing maps separate indices of equal residue
-- statement:
--   Let $P>0$ and $f:\{0..n-1\}\to\mathbb N$ strictly increasing. If $i<j$ and $i\equiv j\pmod P$, then
--   $$
--   \Bigl\lfloor\frac{f(i)}P\Bigr\rfloor<\Bigl\lfloor\frac{f(j)}P\Bigr\rfloor .
--   $$
--
--   Indices congruent modulo $P$ land in different blocks of width $P$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/Alignments.lean#L66-L84

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

open OAI OAI.TreeEdit
universe u
variable {α : Type u} {x y z : List α}

theorem OAI.TreeEdit.div_strict_of_equal_residue {n P : ℕ} (hP : 0 < P)
    (f : Fin n → ℕ) (hf : StrictMono f) {i j : Fin n}
    (hij : i < j) (hmod : i.val % P = j.val % P) : f i / P < f j / P := by sorry
