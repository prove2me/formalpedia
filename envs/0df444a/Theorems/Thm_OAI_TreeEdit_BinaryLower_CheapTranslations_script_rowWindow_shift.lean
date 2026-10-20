-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_CheapTranslations_script_rowWindow_shift
-- name    : OAI.TreeEdit.BinaryLower.CheapTranslations.script_rowWindow_shift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:52:36.209575+00:00
-- url     : https://prove2.me/theorems/192aad7c-293f-4760-acb0-28091d1465a5
-- title:
--   Shifting a window of rows is cheap
-- statement:
--   Here $\mathrm{ed}(x,y)$ is the unit-cost edit distance (insertions, deletions, substitutions), $\mathrm{lcs}(x,y)$ the length of a longest common subsequence, and for words of length $n$ the deficit is $n-\mathrm{lcs}(x,y)$. Let $\mathrm{rows}(j)$ be words all of length $B$, and $W(a)=\mathrm{rows}(a)\,\mathrm{rows}(a+1)\cdots\mathrm{rows}(a+T-1)$. Then for $s\le T$ there is an edit script of length $2sB$ from $W(a)$ to $W(a+s)$; in particular
--   $$
--   \mathrm{ed}\bigl(W(a),W(a+s)\bigr)\le2sB .
--   $$
--
--   Translating the window by $s$ rows deletes $s$ rows at the front and appends $s$ rows at the end.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/CheapTranslations.lean#L126-L149

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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.CheapTranslations
universe u v
variable {α : Type u}

theorem OAI.TreeEdit.BinaryLower.CheapTranslations.script_rowWindow_shift (rows : ℕ → List α)
    (a T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ j, (rows j).length = B) :
    EditScript (rowWindow rows a T) (rowWindow rows (a + s) T)
      (2 * s * B) := by sorry
