-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_constant_on_row_fiber
-- name    : OAI.TreeEdit.BinaryLower.Tagged.constant_on_row_fiber
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:11:56.268991+00:00
-- url     : https://prove2.me/theorems/cb769a36-fd3b-4095-b2a7-c5507aa649a7
-- title:
--   Step-wise constancy on fibers of a monotone map
-- statement:
--   Let $R,S:\{0..n\}\to\mathbb N$ with $R$ monotone and $r\in\mathbb N$. Suppose that whenever consecutive indices $i,i+1$ both lie in the fiber $R=r$, also $S(i)=S(i+1)$. Then $S$ is constant on the fiber:
--   $$
--   R(i)=R(j)=r\ \Longrightarrow\ S(i)=S(j).
--   $$
--
--   Fibers of a monotone map are intervals, so local constancy propagates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean#L97-L133

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

theorem OAI.TreeEdit.BinaryLower.Tagged.constant_on_row_fiber {n : ℕ} (R S : Fin (n + 1) → ℕ)
    (hR : Monotone R) (r : ℕ)
    (hstep : ∀ i : Fin n, R i.castSucc = r → R i.succ = r →
      S i.castSucc = S i.succ) :
    ∀ i j, R i = r → R j = r → S i = S j := by sorry
