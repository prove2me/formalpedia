-- Prove2me | Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedNonsplit_nonsplit_loss_bound_nat
-- name    : OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_bound_nat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:13:43.976017+00:00
-- url     : https://prove2.me/theorems/533bfd7a-16e3-42ed-9c17-011d96383177
-- title:
--   Loss counting over nonsplit rows
-- statement:
--   Let $N$ matches be assigned to rows $\mathrm{row}(i)<T$, with $n_r$ matches in row $r$. Let $S\subseteq\{0..T-1\}$, $W,d\in\mathbb R$, with $n_r\le W$ for all rows and $n_r\le W-d$ for rows $r\notin S$. Then
--   $$
--   d\,(T-|S|)\le TW-N .
--   $$
--
--   Every row outside $S$ loses at least $d$ of its capacity $W$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean#L159-L195

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

theorem OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_bound_nat {N T : ℕ} (row : Fin N → ℕ)
    (S : Finset ℕ) (W d : ℝ)
    (hrow : ∀ i, row i < T) (hS : S ⊆ Finset.range T)
    (hcapacity : ∀ r < T, (natRowCount row r : ℝ) ≤ W)
    (hnonsplit : ∀ r < T, r ∉ S → (natRowCount row r : ℝ) ≤ W - d) :
    d * ((T : ℝ) - S.card) ≤ (T : ℝ) * W - N := by sorry
